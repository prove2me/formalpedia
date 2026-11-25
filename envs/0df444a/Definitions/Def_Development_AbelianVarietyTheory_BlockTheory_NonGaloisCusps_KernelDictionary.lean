-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_KernelDictionary
-- name    : Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_KernelDictionary
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T02:11:08.510784+00:00
-- url     : https://prove2.me/theorems/47160173-606e-4854-a98b-1bc0b7551fa3
-- title:
--   Kernel Dictionary
-- statement:
--   Definitions and structural lemmas for Kernel Dictionary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/KernelDictionary.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MapCSmulMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_RoundDown
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_OfKillsOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB
namespace GlobalTheory.IndefiniteRowSideFullHecke.KernelDictionary
section Generic
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {l : ℕ} (R : Fr l O)
abbrev EmbOver (K : Type) [Field K] [Algebra Qp K] [Algebra K₀ K] (e : K₀ →ₐ[Qp] LL) : Type :=
  {τ : K →ₐ[Qp] LL // ∀ x : K₀, τ (algebraMap K₀ K x) = e x}
def diag (n : ℕ) (a : O⟦X⟧) : LetA O n := fun _ => a
def IsInvFrame (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (jE : R.EE →ₐ[O] W.EE) : Prop :=
  Function.Injective j ∧
  (∀ a : O⟦X⟧, (∃ b, j b = a) ↔ ∀ δ ∈ W.DelF, W.γ₀ δ a = a) ∧
  R.s = W.DelF.card ∧
  Associated (j X) (X ^ R.s) ∧ Associated (j R.E) W.q₀ ∧
  (∀ a, j (R.φ a) = W.φ₀ (j a)) ∧ (∀ a, j (R.γ a) = W.γ₀ W.gam (j a)) ∧
  R.χ = W.χΓ W.gam ∧
  (∀ a, jE (R.ι a) = algebraMap (LetA O n) W.EE (diag n (j a))) ∧
  (∀ x, jE (R.φE x) = W.φE (jE x)) ∧ (∀ x, jE (R.γE x) = W.γE W.gam (jE x))
def KillsN {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (i : ZMod n) (a : O⟦X⟧) : Prop :=
  ∀ y ∈ W.Nl T' i, ∃ x ∈ W.Nl T i, W.map f x = diag n a • y
variable [NeZero n] {R} (jE : R.EE →ₐ[O] W.EE)
def vec {T : LocLat G Qp LL O} {r : ℕ} (b : ZMod n → Fin r → W.DD T) (x : DD R n r) : W.DD T :=
  ∑ i, ∑ k, jE (x i k) • b i k
def vec2 {T : LocLat G Qp LL O} {r : ℕ} (b : ZMod n → Fin r → W.DD T)
    (pr : DD R n r × DD R n r) : W.DD T × W.DD T :=
  (vec W jE b pr.1, vec W jE b pr.2)
def IsCoord (T : LocLat G Qp LL O) {r : ℕ} (S : Sys R n r) (b : ZMod n → Fin r → W.DD T) : Prop :=
  (∀ i k, b i k ∈ W.Nl T i ∧ b i k ∈ W.NΔ T) ∧
  Function.Injective (vec W jE b) ∧
  (∀ y : W.DD T, (∃ x, vec W jE b x = y) ↔ ∀ δ ∈ W.DelF, W.γD T δ y = y) ∧
  (∀ x, vec W jE b x ∈ W.N T ↔ ∀ i, x i ∈ R.N0 r) ∧
  (∀ x, vec W jE b (S.φD x) = W.φD T (vec W jE b x)) ∧
  (∀ x, vec W jE b (S.γD x) = W.γD T W.gam (vec W jE b x))
def IsCl (T : LocLat G Qp LL O) {r : ℕ} (b : ZMod n → Fin r → W.DD T)
    (pr : DD R n r × DD R n r) (c : LatticeCohomology T.L) : Prop :=
  ∃ pr' : ↥(W.wachCocyclesDelta T), (pr' : W.DD T × W.DD T) = vec2 W jE b pr ∧ W.clK T pr' = c
def HerrCmp (T : LocLat G Qp LL O) {r : ℕ} (S : Sys R n r) (b : ZMod n → Fin r → W.DD T) : Prop :=
  (∀ pr, pr ∈ S.Z1 ↔ vec2 W jE b pr ∈ W.wachCocyclesDelta T) ∧
  S.Zf ≤ S.Z1 ∧
  (∀ c : LatticeCohomology T.L, ∃ pr ∈ S.Z1, IsCl W jE T b pr c) ∧
  (∀ pr, IsCl W jE T b pr 0 ↔ pr ∈ S.B1) ∧
  (∀ pr c, IsCl W jE T b pr c → (pr ∈ S.Zf ↔ c ∈ latticeFiniteCohomology PD T.L)) ∧
  ∀ g : ℕ, S.FIN g ↔
    ∃ t : Finset (LatticeCohomology T.L), t.card ≤ g ∧ Submodule.span O (t : Set (LatticeCohomology T.L)) = latticeFiniteCohomology PD T.L
def HomCmp (j : O⟦X⟧ →ₐ[O] O⟦X⟧) {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) {r r' : ℕ}
    {S : Sys R n r} {S' : Sys R n r'} (b : ZMod n → Fin r → W.DD T)
    (b' : ZMod n → Fin r' → W.DD T') (F : Hom S S') : Prop :=
  (∀ x, vec W jE b' (F.fD x) = W.map f (vec W jE b x)) ∧
  (∀ pr c, IsCl W jE T b pr c → IsCl W jE T' b' (F.fD pr.1, F.fD pr.2) (f.H1map c)) ∧
  (f.Onto → F.Good) ∧
  (∀ e : ℕ, F.LiftF e ↔ f.LiftF PD e) ∧
  (∀ x : ℚ, F.ColLe (x : ℝ) ↔ f.ColLe PD x) ∧
  ∀ (i : ZMod n) (a : O⟦X⟧), KillsN W f i (j a) → F.Kills i a
omit [NeZero n] in

def KillsExt (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (T : LocLat G Qp LL O) (𝒦 : ZMod n → O⟦X⟧ → Prop) : Prop :=
  ∀ (Y U : LocLat G Qp LL O) (ι : LatHom T.L Y.L) (pr : LatHom Y.L U.L),
    (∀ g x, U.ρ g x = x) → IsSESLat (Qp := Qp) ι pr → IsCrys PD Y.ρ →
      ∀ (i : ZMod n) (a : O⟦X⟧), 𝒦 i a → KillsN W pr i (j a)
omit [NeZero n] in

def JumpCmp [IsDomain O] (β : ∀ i, Fin R.e ≃ EmbOver K (W.emb i)) (T : LocLat G Qp LL O) {r : ℕ}
    (S : Sys R n r) : Prop :=
  ∀ (i : ZMod n) (τ : Fin R.e) (a : ℤ),
    (S.IsJump i τ a ↔ IsJumpV PD T.ρ (β i τ).1 a) ∧
      (S.count i τ a a : ℤ) = multV PD T.ρ (β i τ).1 a
example (T : LocLat G Qp LL O) (i : ZMod n) : KillsN W (latId T) i 1 := fun y hy =>
  ⟨y, hy, by rw [W.map_id]; exact (one_smul (LetA O n) y).symm⟩
example {T : LocLat G Qp LL O} {r : ℕ} (b : ZMod n → Fin r → W.DD T) : vec W jE b 0 = 0 := by
  simp [vec]
end Generic
variable {l : ℕ} [Fact l.Prime]
instance finiteDimensional_maxUnramifiedSubfield (K : FinExt l) : FiniteDimensional ℚ_[l] ↥(K0 K) :=
  haveI := K.2
  FiniteDimensional.of_injective
    (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
    (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
instance neZero_finrank_maxUnramifiedSubfield (K : FinExt l) : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) :=
  ⟨Module.finrank_pos.ne'⟩
def Dictionary (P : LocPrime l) (H : LocHW l P) (K LL : FinExt l) (h : Good K 1 LL) : Prop :=
  ∃ (R : Fr l ↥(OL LL)) (j : (↥(OL LL))⟦X⟧ →ₐ[↥(OL LL)] (↥(OL LL))⟦X⟧)
    (jE : R.EE →ₐ[↥(OL LL)] (H.W K 1 LL h).EE)
    (β : ∀ i, Fin R.e ≃ EmbOver ↥K.1 ((H.W K 1 LL h).emb i))
    (S : ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), IsCrys (P.PD K) T.ρ →
      Sys R (Module.finrank ℚ_[l] ↥(K0 K)) (Module.finrank ↥(OL LL) ↥T.L.T))
    (b : ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), IsCrys (P.PD K) T.ρ →
      ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Fin (Module.finrank ↥(OL LL) ↥T.L.T) →
        (H.W K 1 LL h).DD T),
    IsInvFrame (H.W K 1 LL h) R j jE ∧
    R.e = Module.finrank ↥(K0 K) ↥K.1 ∧
    (K.1 ≤ MaximalUnramifiedExtension l → R.IsA ∧ j X = (H.W K 1 LL h).π₀₁) ∧
    (¬ K.1 ≤ MaximalUnramifiedExtension l → j X = ∏ δ ∈ (H.W K 1 LL h).DelF, (H.W K 1 LL h).γ₀ δ X) ∧
    (∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (τ : Fin R.e) (ζ : ↥LL.1)
      (τ₁ : ↥(Ks K 1) →ₐ[ℚ_[l]] ↥LL.1), H.IsPt h i ζ τ₁ →
      (∀ (x : ↥K.1) (y : ↥(Ks K 1)), (y : Om l) = (x : Om l) → τ₁ y = (β i τ).1 x) →
      constantCoeff ((H.W K 1 LL h).lev i ζ (diag _ (j X))) =
        algebraMap ↥(OL LL) ↥LL.1 (R.ϖ τ)) ∧
    (∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys (P.PD K) T.ρ),
      IsCoord (H.W K 1 LL h) jE T (S T hT) (b T hT) ∧
      JumpCmp (H.W K 1 LL h) β T (S T hT) ∧
      HerrCmp (H.W K 1 LL h) jE T (S T hT) (b T hT) ∧
      ∀ 𝒦, KillsExt (H.W K 1 LL h) j T 𝒦 → ExtK (S T hT) 𝒦) ∧
    ∀ (T T' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys (P.PD K) T.ρ)
      (hT' : IsCrys (P.PD K) T'.ρ) (f : LatHom T.L T'.L),
      ∃ F : Hom (S T hT) (S T' hT'), HomCmp (H.W K 1 LL h) jE j f (b T hT) (b T' hT') F
def DictionaryAll (P : LocPrime l) (H : LocHW l P) : Prop :=
  ∀ (K LL : FinExt l) (h : Good K 1 LL), Dictionary P H K LL h
end GlobalTheory.IndefiniteRowSideFullHecke.KernelDictionary


