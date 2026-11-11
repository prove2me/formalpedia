-- Prove2me | Definitions.Def_FlexRigidity_Extraction
-- name    : FlexRigidity_Extraction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:26:38.581394+00:00
-- url     : https://prove2.me/theorems/5a9419dd-6f24-4293-a6c4-d61c6c2300ee
-- title:
--   Extraction isometries and recovery channels
-- statement:
--   For each round, isometries $V^{\mathrm A}_i:M^{\mathrm A}_iM'^{\mathrm A}_i\to S^{\mathrm A}_iQ^{\mathrm A}_i$ and $V^{\mathrm B}_i:M^{\mathrm B}_iM'^{\mathrm B}_i\to S^{\mathrm B}_iQ^{\mathrm B}_i$ from Postulate 5.3(iii) for the projector families of (47), CPTP recovery channels $N^{\mathrm A}_i,N^{\mathrm B}_i$ with $N^{\mathrm A}_i[V^{\mathrm A}_i\sigma V^{\mathrm A\dagger}_i]=\sigma$ (likewise for Bob), and the basis vector $|00\rangle_{S_{\mathrm A}S_{\mathrm B}}$ of the dummy registers. `IsAdmissible` states these conditions, with the self-testing bound (41) for the round's families; the milestones hold for every admissible choice.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), §5.3.1, p. 45

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_StoredImpl
import Definitions.Def_FlexRigidity_SelfTestBound
import Definitions.Def_FlexRigidity_IsIsometry
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Extraction isometries and recovery channels** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, §5.3.1, p. 45): for each round `i`, isometries
`V^A_i : M^A_i M′^A_i → S^A_i Q^A_i` and `V^B_i : M^B_i M′^B_i → S^B_i Q^B_i` given by Postulate
5.3(iii) for the full projector families of (47), and CPTP recovery channels `N^A_i`, `N^B_i` with
`N^A_i[V^A_i σ (V^A_i)†] = σ` (and likewise for Bob). `s0` is the fixed basis vector `|00⟩` of
`S_A S_B` used for the dummy registers of `G^test_i`.

`IsAdmissible` says, for rounds `i < n`: `V^A_i, V^B_i` are isometries satisfying the
self-testing bound (41) for the families `({H^x_{i,a}}_a)_x`, `({K^y_{i,b}}_b)_y`; `N^A_i, N^B_i` are
channels and left inverses of the isometries. The milestones are stated for **every** admissible
choice.

**Formalization Note** `Q^A_i = Fin (qA i)`, `Q^B_i = Fin (qB i)`. -/
structure Extraction (X Y A B SA SB : Type) (I : StoredImpl X Y A B) where
  /-- dimension of `Q^A_i` -/
  qA : ℕ → ℕ
  /-- dimension of `Q^B_i` -/
  qB : ℕ → ℕ
  /-- `V^A_i` -/
  VA : (i : ℕ) → Matrix (SA × Fin (qA i)) (Fin (I.dA i) × Fin (I.kA i + 1)) ℂ
  /-- `V^B_i` -/
  VB : (i : ℕ) → Matrix (SB × Fin (qB i)) (Fin (I.dB i) × Fin (I.kB i + 1)) ℂ
  /-- `N^A_i` -/
  NA : (i : ℕ) → Superop (SA × Fin (qA i)) (Fin (I.dA i) × Fin (I.kA i + 1))
  /-- `N^B_i` -/
  NB : (i : ℕ) → Superop (SB × Fin (qB i)) (Fin (I.dB i) × Fin (I.kB i + 1))
  /-- the basis vector `|00⟩_{S_A S_B}` -/
  s0 : SA × SB

/-- Admissibility of the extraction data for rounds `i < n`. -/
def Extraction.IsAdmissible {X Y A B SA SB : Type} [Fintype X] [Fintype Y] [Fintype A]
    [Fintype B] [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    {I : StoredImpl X Y A B} (G : Game X Y A B) (Rz : Realization X Y A B SA SB)
    (van : ℝ → ℝ) (Ex : Extraction X Y A B SA SB I) (n : ℕ) : Prop :=
  ∀ i < n, IsIsometry (Ex.VA i) ∧ IsIsometry (Ex.VB i) ∧
    SelfTestBound G Rz van (I.H i) (I.K i) (Ex.VA i) (Ex.VB i) ∧
    IsChannel (Ex.NA i) ∧ IsChannel (Ex.NB i) ∧
    (∀ σ, Ex.NA i (Ex.VA i * σ * (Ex.VA i)ᴴ) = σ) ∧ (∀ σ, Ex.NB i (Ex.VB i * σ * (Ex.VB i)ᴴ) = σ)

end FlexRigidity


