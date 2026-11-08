-- Prove2me | Definitions.Def_EntangledPIR_testProj
-- name    : EntangledPIR_testProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:44.776367+00:00
-- url     : https://prove2.me/theorems/66d9b693-0d57-4415-8d89-97d463267ba9
-- title:
--   One copy of the lookup: $U_g$, $V_a$, the test projectors $\Pi^a_f$ and the Bell state
-- statement:
--   One copy of the lookup, for a table $g:\{0,1\}^d\to\{0,1\}^m$. A server holds an address register $\mathsf P$ of $d$ qubits and an output register $\mathsf Y_z$ of $m$ qubits for every $z\in\{0,1\}^d$, so $r=d+m2^d$ qubits. The two servers share $|\Phi^+\rangle^{\otimes r}$. On a basis state,
--
--   $$U_g|q\rangle_{\mathsf P}\bigotimes_{z}|c_z\rangle_{\mathsf Y_z}=|q\rangle_{\mathsf P}\bigotimes_{z}|c_z\oplus g(q\oplus z)\rangle_{\mathsf Y_z}.$$
--
--   The test is defined, for $a,f\in\{0,1\}^d$, by
--
--   $$V_a=(U_g)_{\mathsf B}X^a_{\mathsf P'},\qquad \Pi^a_f=V_a^\dagger\bigl(H^{\otimes d}|f\rangle\langle f|H^{\otimes d}\bigr)_{\mathsf P'}V_a .$$
--
--   The module also defines: the Kraus operator $(H^{\otimes d}|e\rangle\langle e|H^{\otimes d})_{\mathsf P}U_gX^a_{\mathsf P}$ of the operation of A with outcome $e$; the projectors $|u\rangle\langle u|_{\mathsf Y_z}$; and the Kraus operator of the computation of B with mask $b$ and outcomes $J,v$, which measures $\mathsf P'$ and then $\mathsf Y'_{J\oplus b}$.
--
--   **Formalization Note** The registers $\mathsf P',\mathsf Y'_z$ of B have the same index type as those of A, because the paper identifies them (p.21), so $(U_g)_{\mathsf B}$ is the matrix $U_g$. The environment $|e\rangle$ of the measurement of A is its classical record of $e$.
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), §4, (4.1), (4.3), pp.19–21

import Definitions.Def_EntangledPIR_Bits

/-!
Mantri, *Private Information Retrieval from Two Entangled Servers*, manuscript (Nov. 2026), §4,
pp.19–22: one copy of the lookup.
-/

open Matrix
open scoped Kronecker

namespace EntangledPIR

/-- The registers of one server in one copy of the lookup, p.19: an address register `P` of `d`
qubits and an output register `Y_z` of `m` qubits for every `z ∈ {0,1}^d`. An element is a
computational basis state `(q, c)`, `q` the content of `P`, `c z` the content of `Y_z`.
**Formalization Note.** `P′`, `Y′_z` at B have the same type: the paper identifies `P` with `P′`
and `Y_z` with `Y′_z` (p.21), so `(U_g)_B` is the same matrix as `U_g`. -/
abbrev CopyReg (d m : ℕ) : Type := Bits d × (Bits d → Bits m)

/-- The qubits of one server in one copy: `d` address qubits and `m` qubits for each `Y_z`, so
`r = d + m 2^d` of them, p.19. -/
abbrev CopyQubit (d m : ℕ) : Type := Fin d ⊕ (Bits d × Fin m)

/-- The value of each qubit in a basis state of a copy. -/
def qubitsOf {d m : ℕ} (s : CopyReg d m) : CopyQubit d m → Bool :=
  Sum.elim s.1 (fun p => s.2 p.1 p.2)

/-- The permutation of basis states of (4.1), p.19:
`(q, (c_z)_z) ↦ (q, (c_z ⊕ g(q ⊕ z))_z)`. -/
def UgFun {d m : ℕ} (g : Bits d → Bits m) (s : CopyReg d m) : CopyReg d m :=
  (s.1, fun z => bxor (s.2 z) (g (bxor s.1 z)))

/-- The unitary `U_g` of (4.1), p.19, as the permutation matrix of `UgFun`. -/
def Ug {d m : ℕ} (g : Bits d → Bits m) : Matrix (CopyReg d m) (CopyReg d m) ℂ :=
  Matrix.of fun s s' => if s = UgFun g s' then 1 else 0

/-- An operator on the address register `P` (or `P′`) of a copy: `O_P ⊗ 1`. -/
def onAddr {d m : ℕ} (O : Matrix (Bits d) (Bits d) ℂ) : Matrix (CopyReg d m) (CopyReg d m) ℂ :=
  O ⊗ₖ (1 : Matrix (Bits d → Bits m) (Bits d → Bits m) ℂ)

/-- `V_a = (U_g)_B X^a_{P′}` of (4.3), p.21. -/
def Va {d m : ℕ} (g : Bits d → Bits m) (a : Bits d) : Matrix (CopyReg d m) (CopyReg d m) ℂ :=
  Ug g * onAddr (pauliXs a)

/-- The test projector `Π^a_f = V_a^† (H^{⊗d}|f⟩⟨f|H^{⊗d})_{P′} V_a` of (4.3), p.21. -/
noncomputable def testProj {d m : ℕ} (g : Bits d → Bits m) (a f : Bits d) :
    Matrix (CopyReg d m) (CopyReg d m) ℂ :=
  (Va g a)ᴴ * onAddr (hadProj f) * Va g a

/-- The Kraus operator of the outcome `e` of the operation of A with mask `a`, p.19: apply
`U_g X^a_P`, then measure `P` in the Hadamard basis. It is the operator
`(H^{⊗d}|e⟩⟨e|H^{⊗d})_P U_g X^a_P` of the proof of Lemma 4.3, p.22.
**Formalization Note.** The environment `|e⟩` of the measurement is the classical record of the
outcome `e`; in the protocol it is the message in the classical history of A. -/
noncomputable def opKraus {d m : ℕ} (g : Bits d → Bits m) (a e : Bits d) :
    Matrix (CopyReg d m) (CopyReg d m) ℂ :=
  onAddr (hadProj e) * Ug g * onAddr (pauliXs a)

/-- The projector `|u⟩⟨u|_{Y_z}` of the measurement of `Y_z` in the computational basis, p.19. -/
def outProj {d m : ℕ} (z : Bits d) (u : Bits m) : Matrix (CopyReg d m) (CopyReg d m) ℂ :=
  Matrix.diagonal fun s => if s.2 z = u then 1 else 0

/-- The Kraus operator of the computation of B with mask `b`, p.19, with outcomes `J`, `v`:
measure `P′` in the computational basis, obtaining `J`, and then `Y′_K` for `K = J ⊕ b`, obtaining
`v`. -/
def computeKraus {d m : ℕ} (b J : Bits d) (v : Bits m) : Matrix (CopyReg d m) (CopyReg d m) ℂ :=
  outProj (bxor J b) v * onAddr (basisProj J)

/-- The state `|Φ+⟩^{⊗r}` of one copy, `r = d + m 2^d`, p.19: amplitude `2^{-r/2}` on the basis
states where both sides hold the same string, and zero otherwise. -/
noncomputable def bellCopy (d m : ℕ) : CopyReg d m × CopyReg d m → ℂ :=
  fun p => if p.1 = p.2 then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ^ (d + m * 2 ^ d) else 0

/-- `Θ_A ⊗ 1` on the two servers' registers of a copy. -/
def leftOp {d m : ℕ} (Θ : Matrix (CopyReg d m) (CopyReg d m) ℂ) :
    Matrix (CopyReg d m × CopyReg d m) (CopyReg d m × CopyReg d m) ℂ :=
  Θ ⊗ₖ (1 : Matrix (CopyReg d m) (CopyReg d m) ℂ)

/-- `1 ⊗ Θ_B` on the two servers' registers of a copy. -/
def rightOp {d m : ℕ} (Θ : Matrix (CopyReg d m) (CopyReg d m) ℂ) :
    Matrix (CopyReg d m × CopyReg d m) (CopyReg d m × CopyReg d m) ℂ :=
  (1 : Matrix (CopyReg d m) (CopyReg d m) ℂ) ⊗ₖ Θ

/-- The squared norm of a vector, the probability of an unnormalized post-measurement vector. -/
noncomputable def normSq {ι : Type} [Fintype ι] (v : ι → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

end EntangledPIR


