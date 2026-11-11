-- Prove2me | Definitions.Def_FlexRigidity_roundT
-- name    : FlexRigidity_roundT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:29:23.734352+00:00
-- url     : https://prove2.me/theorems/b46c0960-398c-4a16-8a85-3f8e7cbb54e3
-- title:
--   The channel $\mathcal T_i$, eq. (49)
-- statement:
--   From $Z_iS_iJ_i$ to $C_iO_iM_{i+1}$: on test rounds $\mathcal T_i$ traces out the dummy $S^{\mathrm A}S^{\mathrm B}$ and keeps $A_iJ_i$; on generation rounds it applies $(L^{\mathrm A,x}_i\otimes L^{\mathrm B,\mathrm{gen}}_i)\circ(\mathrm{id}_{A_i}\otimes N^{\mathrm A}_i\otimes N^{\mathrm B}_i)$, with $L^{\mathrm A,x}_i[|a\rangle\langle a|\otimes\sigma]=|a\rangle\langle a|\otimes L^{\mathrm A,x,a}_i[\sigma]$ and $L^{\mathrm B,\mathrm{gen}}_i[\sigma]=\mathcal E^{\mathrm B,\mathrm{gen}}_i[\operatorname{Tr}_{M'^{\mathrm B}_i}\sigma]$; the classical $U_iX_iC_i$ are kept.
--
--   **Formalization Note** $\mathcal T_i$ pinches $Z_i$ and the two summands of $J_i$, and processes the test summand and the generation summand with the two maps above. On the inputs that occur this is (49); on the two sectors that never occur the same maps are used, so that $\mathcal T_i$ is CPTP on all inputs, as Postulate Set 4.1 requires.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), eq. (49), p. 46

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_Extraction
import Definitions.Def_FlexRigidity_RoundJ
import Definitions.Def_FlexRigidity_RoundO
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **The channel `T_i`, eq. (49)** (Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444,
artifact sha256 8c67699d…, p. 46), from `Z_i S_i J_i` to `C_i O_i M_{i+1}` with
`O_i = U_i X_i Y_i A_i B_i`:
`T_i[|test,x,c⟩⟨…| ⊗ ρ_{S_i J_i}] = |test,x,c⟩⟨…| ⊗ ρ_{A_i J_i}` (the dummy `S^A S^B` traced out) and
`T_i[|gen,x,c⟩⟨…| ⊗ ρ_{S_i J_i}] = |gen,x,c⟩⟨…| ⊗ (L^{A,x}_i ⊗ L^{B,gen}_i) ∘ (id_{A_i} ⊗ N^A_i ⊗ N^B_i)[ρ_{S_i J_i}]`,
with `L^{A,x}_i[|a⟩⟨a| ⊗ σ] = |a⟩⟨a| ⊗ L^{A,x,a}_i[σ]` and
`L^{B,gen}_i[σ] = E^{B,gen}_i[Tr_{M′^B_i} σ]` (which sets `B_i = ∅`).

**Formalization Note** `T_i` pinches the classical register `Z_i = U_i X_i C_i` and the two
orthogonal summands of `J_i` (`RoundJ`). On the test summand `inr (y, b, m)` it traces out
`S^A S^B` and keeps `(a, y, b, m)`; on the generation summand `inl (y, q)` it pinches `A_i` and
applies `(L^{A,x}_i ⊗ L^{B,gen}_i) ∘ (N^A_i ⊗ N^B_i)`; the output record is `(c, (u, x, y, a, b))`
with `u`, `x`, `c` copied from `Z_i`. On the inputs that occur (generation rounds in the `inl`
summand, test rounds in the `inr` summand) this is (49); the two other sectors, which never
occur, are processed by the same two maps, so that `T_i` is CPTP on all inputs, as Postulate
Set 4.1 requires. -/
def roundT {X Y A B SA SB : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype SA]
    [Fintype SB] [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] [DecidableEq SA]
    [DecidableEq SB] {I : StoredImpl X Y A B} (Ex : Extraction X Y A B SA SB I) (i : ℕ) :
    Superop ((Bool × X × Option Bool) × (A × SA × SB) ×
        RoundJ Y B (Ex.qA i) (Ex.qB i) (I.dA (i + 1)) (I.dB (i + 1)))
      ((Option Bool × RoundO X Y A B) × (Fin (I.dA (i + 1)) × Fin (I.dB (i + 1)))) :=
  fun ρ => Matrix.of fun p q =>
    match p, q with
    | ((c, (u, x, y, a, b)), m), ((c', (u', x', y', a', b')), m') =>
      if u = u' ∧ x = x' ∧ c = c' then
        (∑ s : SA × SB, ρ ((u, x, c), (a, s.1, s.2), Sum.inr (y, b, m))
            ((u, x, c), (a', s.1, s.2), Sum.inr (y', b', m'))) +
        (if a = a' ∧ b = none ∧ b' = none then
          let Xa : Matrix ((SA × Fin (Ex.qA i)) × (SB × Fin (Ex.qB i)))
              ((SA × Fin (Ex.qA i)) × (SB × Fin (Ex.qB i))) ℂ :=
            Matrix.of fun v w => ρ ((u, x, c), (a, v.1.1, v.2.1), Sum.inl (y, (v.1.2, v.2.2)))
              ((u, x, c), (a, w.1.1, w.2.1), Sum.inl (y', (w.1.2, w.2.2)))
          QAlgorithms.Papers.Independent.Information100.P62.tensorChannel (I.LA i x a) (fun τ => I.EBg i (leftMarginal τ))
            (QAlgorithms.Papers.Independent.Information100.P62.tensorChannel (Ex.NA i) (Ex.NB i) Xa) m m'
         else 0)
      else 0

end FlexRigidity


