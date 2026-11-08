-- Prove2me | Definitions.Def_EntangledPIR_zetaAE
-- name    : EntangledPIR_zetaAE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:14:39.546201+00:00
-- url     : https://prove2.me/theorems/2149a2fb-e9c4-42d0-9787-c8eb8945bf48
-- title:
--   The states $\rho_{a,e}$ and $\zeta^{a,e}_x$
-- statement:
--   For masks $a$ and a well-formed report $e$, $\rho_{a,e}$ is the joint state of all registers of A and of the copies of B at the moment A sends its outcomes, projected onto the value $(a,e)$, carrying the probability $2^{-4kd}$ of $a$. With the projectors $\Pi_{i,j}=\Pi^{a_{i,j}}_{e_{i,j}}$ for the tables $F_i$, $\ell=4$, and $\mu_x$ the distribution of the queries on index $x$,
--
--   $$\zeta^{a,e}_x=R^a_x\bigl(A(\rho_{a,e})\bigr).$$
--
--   **Formalization Note** The classical values $a,e$ are the index of the family and are not in a register of $\rho_{a,e}$. In `rhoAE` the honest B is idle in round 0 and its register outside the copies is traced out.
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), Claim C.4 and the text before it, p.59; (5.5), p.28

import Definitions.Def_EntangledPIR_PrivateAgainstA
import Definitions.Def_EntangledPIR_CutChoose

/-!
Mantri, *Private Information Retrieval from Two Entangled Servers*, manuscript (Nov. 2026), Claim C.4,
p.59, and p.28: the states `ρ_{a,e}` and `ζ^{a,e}_x` of the proof of privacy against A.
-/

open Matrix
open scoped Kronecker

namespace EntangledPIR

/-- The remainders `E_{i,j}` of the copies of Protocol 1 in the setting of §3: all registers of a copy other
than the address register, p.28. -/
abbrev ProtoRest (n m lam : ℕ) : Fin (shareCount n lam) × Fin 4 → Type :=
  fun _ => Bits (queryLen n lam) → Bits m

/-- The projectors `Π_{i,j} = Π^{a_{i,j}}_{e_{i,j}}` for the table `F_i`, p.28. -/
noncomputable def protoTests {n m : ℕ} (lam : ℕ) (F : Bits n → Bits m)
    (a e : CopyIdx (shareCount n lam) → Bits (queryLen n lam)) :
    ∀ c, Matrix (CopyB (queryLen n lam) (ProtoRest n m lam) c)
      (CopyB (queryLen n lam) (ProtoRest n m lam) c) ℂ :=
  fun c => testProj (table lam F c.1) (a c) (e c)

/-- The state `ρ_{a,e}`, p.59: the joint state of all registers of A and of the copies of B at the moment A
sends its outcomes, projected onto masks `a` and well-formed report `e`, with the registers of B outside the
copies traced out. It carries the probability `2^{-4kd}` of the masks. The registers of A hold `a, e` in the
history, so here `R` is `SA.Reg 1` and the classical values are the index of `ρ_{a,e}`. The honest B is idle in
round 0, on message `[]`. -/
noncomputable def rhoAE {n m : ℕ} (lam : ℕ) (SA : Strategy (msgBound n m lam)) (RB0 : Type)
    [Fintype RB0] [DecidableEq RB0]
    (ρ₀ : Matrix (SA.Reg 0 × (Copies n m lam × RB0)) (SA.Reg 0 × (Copies n m lam × RB0)) ℂ)
    (a e : CopyIdx (shareCount n lam) → Bits (queryLen n lam)) :
    Matrix (SA.Reg 1 × Copies n m lam) (SA.Reg 1 × Copies n m lam) ℂ :=
  let I := SA.instr 0 [] (serMat a)
  let o := BitStr.ofList (msgBound n m lam) (serMat e)
  let σ : Matrix (SA.Reg 1 × (Copies n m lam × RB0)) (SA.Reg 1 × (Copies n m lam × RB0)) ℂ :=
    ((2 : ℂ) ^ (4 * shareCount n lam * queryLen n lam))⁻¹ •
      ∑ c, (I.K o c ⊗ₖ (1 : Matrix (Copies n m lam × RB0) (Copies n m lam × RB0) ℂ)) * ρ₀ *
        (I.K o c ⊗ₖ (1 : Matrix (Copies n m lam × RB0) (Copies n m lam × RB0) ℂ))ᴴ
  Matrix.of fun p q => ∑ r0, σ (p.1, (p.2, r0)) (q.1, (q.2, r0))

/-- The state `ζ^{a,e}_x = R^a_x(A(ρ_{a,e}))` of Claim C.4, p.59, with `R^a_x` the map (5.5), `A` the map (3.5) for
`Π_{i,j} = Π^{a_{i,j}}_{e_{i,j}}`, `ℓ = 4`, and `µ_x` the distribution of the queries on index `x`. -/
noncomputable def zetaAE {n m : ℕ} (lam : ℕ) (F : Bits n → Bits m) (SA : Strategy (msgBound n m lam))
    (RB0 : Type) [Fintype RB0] [DecidableEq RB0]
    (ρ₀ : Matrix (SA.Reg 0 × (Copies n m lam × RB0)) (SA.Reg 0 × (Copies n m lam × RB0)) ℂ)
    (a e : CopyIdx (shareCount n lam) → Bits (queryLen n lam)) (x : Bits n) :
    Matrix (Positions (shareCount n lam) 4 × (SA.Reg 1 × ShareVec (shareCount n lam) (queryLen n lam)))
      (Positions (shareCount n lam) 4 × (SA.Reg 1 × ShareVec (shareCount n lam) (queryLen n lam))) ℂ :=
  RmapShift (d := queryLen n lam) (E := ProtoRest n m lam) (R := SA.Reg 1)
    (fun t i => a (i, t i)) (queryDist lam x)
    (Amap (protoTests lam F a e) (rhoAE lam SA RB0 ρ₀ a e))

end EntangledPIR


