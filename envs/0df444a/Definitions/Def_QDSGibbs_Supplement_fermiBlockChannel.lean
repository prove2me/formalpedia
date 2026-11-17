-- Prove2me | Definitions.Def_QDSGibbs_Supplement_fermiBlockChannel
-- name    : QDSGibbs_Supplement_fermiBlockChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:27:33.653933+00:00
-- url     : https://prove2.me/theorems/4a74d95f-50d9-4753-9ef7-460b22a85f33
-- title:
--   Fermionic QBP block channels $\Phi_B(H,T)=e^{T\mathcal K_B}$ with filtered Majorana jumps, and the sampler $L=\ell^{-D}\sum_B(\Phi_B-\mathrm{id})$
-- statement:
--   For the Fermi–Hubbard Hamiltonian $H$ and a block $B$:
--
--   1. The **QBP operator** $O_B=O_B(1)$ (7.15): $O_B'(v)=-\frac\beta4F_{H-(1-v)W_{\partial B}}(W_{\partial B})O_B(v)$, $O_B(0)=I$, with $F$ the QBP transform (3.2).
--   2. The **jumps** (7.17) $J_{B;i,s,r}=2^{-1/2}(1+e^{\beta\,\mathrm{ad}_{H_B}})^{-1/2}(\gamma_{i,s,r})$ and $L_{B;i,s,r}=O_BJ_{B;i,s,r}O_B^{-1}$, for $i\in B$, $s\in\{\uparrow,\downarrow\}$, $r\in\{1,2\}$.
--   3. (7.18) $\mathcal T_B(X)=\sum L XL^*$, $S_B=\sum L^*L$, $G_B=G_H(S_B)$, $$\mathcal K_B(X)=\mathcal T_B(X)-\tfrac12\{S_B,X\}-i[G_B,X],\qquad \Phi_B(H,T)=e^{T\mathcal K_B}.$$
--   4. The **sampler** $L=\ell^{-D}\sum_B(\Phi_B(H,T)-\mathrm{id})$ over all nonempty labelled cubes of side $\ell$.
--
--   **Formalization Note** $F$, $G_H$, the Bohr-frequency calculus and the exponential series are the base mission's `qbpF`, `qbpG`, `bohrCalc`, `sexp`; the ODE solution is chosen by `Classical.epsilon` as in the base `qbpPathOp`. $G_B$ uses the full Hamiltonian $H$, and the filter uses the block Hamiltonian $H_B$.
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), (7.15) p.65, (7.17) and (7.18) p.66, Theorem 1.1 p.6

import Mathlib
import Definitions.Def_QDSGibbs_blockChannel
import Definitions.Def_QDSGibbs_Supplement_fhLattice

open scoped Matrix

namespace QDSGibbs.Supplement

/-- The **fermionic QBP operator** `O_B = O_B(1)`, where
`O′_B(v) = −(β/4) F_{H − (1−v) W_∂B}(W_∂B) O_B(v)`, `O_B(0) = I` (Rouzé–Stilck França,
arXiv:2610.03578, held file sha256 ede55815…, (7.15), p.65), with `F` the QBP transform (3.2).

**Formalization Note** `F` is the base `qbpF`. The path is chosen by `Classical.epsilon` among the
solutions on all of `ℝ` (derivatives entrywise), exactly as the base `qbpPathOp`; the coefficient is
continuous, so the linear ODE has a unique global solution whose value at `1` is the paper's. -/
noncomputable def fqbpOp {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : ℕ} (β : ℝ)
    (H : FermiHubbardMix.HamData Λ M) (B : Finset Λ) : FermiHubbardMix.Op M :=
  (Classical.epsilon fun O : ℝ → FermiHubbardMix.Op M => O 0 = 1 ∧
    ∀ (u : ℝ) (x y : FermiCap.Gaussian.Qubits M), HasDerivAt (fun s => O s x y)
      (((-(β / 4)) • qbpF β (H.ham - (1 - u) • crossF H B) (crossF H B) * O u) x y) u) 1

/-- The **dressed filtered Majorana jumps** (arXiv:2610.03578, (7.17), p.66):
`J_{B;i,s,r} = 2^{−1/2} (1 + e^{β ad_{H_B}})^{−1/2}(γ_{i,s,r})`, `L_{B;i,s,r} = O_B J_{B;i,s,r} O_B^{−1}`.

**Formalization Note** The filter is the base Bohr-frequency calculus `bohrCalc` of the block
Hamiltonian `H_B` (2.7) with `q(ω) = (1 + e^{βω})^{−1/2}`; `⁻¹` is Mathlib's matrix inverse (`O_B` is
invertible). -/
noncomputable def fJump {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : ℕ} (β : ℝ)
    (ord : Λ × Fin 2 ≃ Fin M) (H : FermiHubbardMix.HamData Λ M) (B : Finset Λ) (i : Λ)
    (s r : Fin 2) : FermiHubbardMix.Op M :=
  fqbpOp β H B *
    (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • bohrCalc (hamOnF H B)
      (fun ω => (((Real.sqrt (1 + Real.exp (β * ω)))⁻¹ : ℝ) : ℂ)) (majF ord i s r) *
    (fqbpOp β H B)⁻¹

/-- The jump map `T_B(X) = Σ_{i ∈ B} Σ_{s,r} L_{B;i,s,r} X L*_{B;i,s,r}` (arXiv:2610.03578, (7.18),
p.66). -/
noncomputable def fT {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : ℕ} (β : ℝ)
    (ord : Λ × Fin 2 ≃ Fin M) (H : FermiHubbardMix.HamData Λ M) (B : Finset Λ)
    (X : FermiHubbardMix.Op M) : FermiHubbardMix.Op M :=
  ∑ i ∈ B, ∑ s : Fin 2, ∑ r : Fin 2, fJump β ord H B i s r * X * (fJump β ord H B i s r)ᴴ

/-- The loss operator `S_B = Σ_{i ∈ B} Σ_{s,r} L*_{B;i,s,r} L_{B;i,s,r}` (arXiv:2610.03578, (7.18),
p.66). -/
noncomputable def fS {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : ℕ} (β : ℝ)
    (ord : Λ × Fin 2 ≃ Fin M) (H : FermiHubbardMix.HamData Λ M) (B : Finset Λ) :
    FermiHubbardMix.Op M :=
  ∑ i ∈ B, ∑ s : Fin 2, ∑ r : Fin 2, (fJump β ord H B i s r)ᴴ * fJump β ord H B i s r

/-- The **fermionic block generator** `K_B(X) = T_B(X) − ½{S_B, X} − i[G_B, X]`, `G_B = G_H(S_B)`
with the full Hamiltonian `H` (arXiv:2610.03578, (7.18), p.66).

**Formalization Note** `G_H` is the base coherent map `qbpG β H` (`(i/2) tanh((β/4) ad_H)`, (3.12)). -/
noncomputable def fK {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : ℕ} (β : ℝ)
    (ord : Λ × Fin 2 ≃ Fin M) (H : FermiHubbardMix.HamData Λ M) (B : Finset Λ)
    (X : FermiHubbardMix.Op M) : FermiHubbardMix.Op M :=
  fT β ord H B X - (1 / 2 : ℂ) • (fS β ord H B * X + X * fS β ord H B) -
    Complex.I • (qbpG β H.ham (fS β ord H B) * X - X * qbpG β H.ham (fS β ord H B))

/-- The **fermionic block channel** `Φ_B(H, T) = e^{T K_B}` (arXiv:2610.03578, (7.18), p.66), with the
base exponential series `sexp`. -/
noncomputable def fermiBlockChannel {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : ℕ} (β : ℝ)
    (ord : Λ × Fin 2 ≃ Fin M) (H : FermiHubbardMix.HamData Λ M) (B : Finset Λ) (T : ℝ) :
    FermiHubbardMix.Op M → FermiHubbardMix.Op M :=
  sexp (fK β ord H B) T

/-- The **fermionic block sampler** `L = ℓ^{−D} Σ_B (Φ_B(H, T) − id)` over all nonempty labelled cubes
of side `ℓ` (arXiv:2610.03578, Theorem 1.1, p.6; p.66). -/
noncomputable def fermiSampler {D M : ℕ} (Λ : Finset (Fin D → ℤ)) (β : ℝ)
    (ord : Λ × Fin 2 ≃ Fin M) (H : FermiHubbardMix.HamData Λ M) (ℓ : ℕ) (T : ℝ)
    (X : FermiHubbardMix.Op M) : FermiHubbardMix.Op M :=
  (((ℓ : ℂ) ^ D)⁻¹) • ∑ z ∈ cubeLabels Λ ℓ, (fermiBlockChannel β ord H (cube Λ ℓ z) T X - X)

end QDSGibbs.Supplement


