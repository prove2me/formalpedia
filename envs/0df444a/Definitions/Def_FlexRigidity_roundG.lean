-- Prove2me | Definitions.Def_FlexRigidity_roundG
-- name    : FlexRigidity_roundG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:29:08.531055+00:00
-- url     : https://prove2.me/theorems/bf0ce996-9788-4dda-bad5-cdf580507a23
-- title:
--   The channel $\mathcal G_i=\gamma\mathcal G^{\mathrm{test}}_i+(1-\gamma)\mathcal G^{\mathrm{gen}}_i$, eq. (48)
-- statement:
--   From $M_i=M^{\mathrm A}_iM^{\mathrm B}_i$ to $Z_iS_iJ_i$, $Z_i=U_iX_iC_i$, $S_i=A_iS^{\mathrm A}_iS^{\mathrm B}_i$:
--   $$\mathcal G^{\mathrm{gen}}_i[\rho]=\sum_xP_X(x)|\mathrm{gen},x,\varnothing,\mathrm{gen}\rangle\langle\cdot|\otimes(V^{\mathrm A}_i\otimes V^{\mathrm B}_i)\big[(\mathcal M^{\mathrm A,x}_i\otimes\mathrm{id})[\rho]\otimes|0\rangle\langle0|_{M'^{\mathrm B}_i}\big](V^{\mathrm A}_i\otimes V^{\mathrm B}_i)^\dagger,$$
--   with $\mathcal M^{\mathrm A,x}_i[\rho]=\sum_a|a\rangle\langle a|\otimes H^x_{i,a}(\rho\otimes|0\rangle\langle0|)H^x_{i,a}$, and $\mathcal G^{\mathrm{test}}_i[\rho]=|00\rangle\langle00|_{S^{\mathrm A}S^{\mathrm B}}\otimes\mathcal E^{\mathrm{test}}_i[\rho]$, the test branch of the real channel.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), eq. (48), pp. 45–46

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_Extraction
import Definitions.Def_FlexRigidity_RoundJ
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **The channel `G_i = γ G^test_i + (1−γ) G^gen_i`, eq. (48)** (Arqand–Kundu–Tan, *Flexible
rigidity*, arXiv:2610.00444, artifact sha256 8c67699d…, pp. 45–46), from `M_i = M^A_i M^B_i` to
`Z_i S_i J_i` with `Z_i = U_i X_i C_i`, `S_i = A_i S^A_i S^B_i`:
`G^gen_i[ρ] = Σ_x P_X(x) |gen,x,∅,gen⟩⟨…| ⊗ (V^A_i ⊗ V^B_i)[(M^{A,x}_i ⊗ id)[ρ] ⊗ |0⟩⟨0|_{M′^B_i}](V^A_i ⊗ V^B_i)†`
with `M^{A,x}_i[ρ] = Σ_a |a⟩⟨a| ⊗ H^x_{i,a}(ρ ⊗ |0⟩⟨0|)H^x_{i,a}`, and
`G^test_i[ρ] = |00⟩⟨00|_{S^A S^B} ⊗ E^test_i[ρ]`, `E^test_i[ρ] = Σ_{x,y} P_{XY}(x,y) |test,x,y⟩⟨…| ⊗ (E^{A,x}_i ⊗ E^{B,test,y}_i)[ρ]`
with the record `c = V(x,y,a,b)`.

**Formalization Note** `Z_i = (u, x, c)` is `Bool × X × Option Bool`; the generation part of `J_i`
is `inl (∅, (q_A, q_B))` and the test part `inr (y, b, (m^A_{i+1}, m^B_{i+1}))` (`RoundJ`). Both
branches are block diagonal in the classical registers. -/
def roundG {X Y A B SA SB : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] [DecidableEq SA] [DecidableEq SB]
    (G : Game X Y A B) (Rz : Realization X Y A B SA SB) (γ : ℝ) {I : StoredImpl X Y A B}
    (Ex : Extraction X Y A B SA SB I) (i : ℕ) :
    Superop (Fin (I.dA i) × Fin (I.dB i))
      ((Bool × X × Option Bool) × (A × SA × SB) ×
        RoundJ Y B (Ex.qA i) (Ex.qB i) (I.dA (i + 1)) (I.dB (i + 1))) :=
  fun ρ => Matrix.of fun p q =>
    match p, q with
    | ((false, x, none), (a, sa, sb), Sum.inl (none, (qa, qb))),
      ((false, x', none), (a', sa', sb'), Sum.inl (none, (qa', qb'))) =>
        if x = x' ∧ a = a' then
          let W := Matrix.kronecker (Ex.VA i * I.H i x a *
              Matrix.of (fun (u : Fin (I.dA i) × Fin (I.kA i + 1)) (v : Fin (I.dA i)) =>
                if u = (v, 0) then (1 : ℂ) else 0))
            (Ex.VB i * Matrix.of (fun (u : Fin (I.dB i) × Fin (I.kB i + 1)) (v : Fin (I.dB i)) =>
                if u = (v, 0) then (1 : ℂ) else 0))
          (((1 - γ) * Rz.PX x : ℝ) : ℂ) * (W * ρ * Wᴴ) ((sa, qa), (sb, qb)) ((sa', qa'), (sb', qb'))
        else 0
    | ((true, x, some c), (a, sa, sb), Sum.inr (some y, some b, m)),
      ((true, x', some c'), (a', sa', sb'), Sum.inr (some y', some b', m')) =>
        if x = x' ∧ c = c' ∧ a = a' ∧ y = y' ∧ b = b' ∧ c = G.V x y a b ∧
            (sa, sb) = Ex.s0 ∧ (sa', sb') = Ex.s0 then
          ((γ * G.PXY x y : ℝ) : ℂ) * QAlgorithms.Papers.Independent.Information100.P62.tensorChannel (I.instA i x a) (I.instB i y b) ρ m m'
        else 0
    | _, _ => 0

end FlexRigidity


