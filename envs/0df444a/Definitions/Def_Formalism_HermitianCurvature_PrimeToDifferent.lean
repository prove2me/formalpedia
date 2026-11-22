-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
-- name    : Formalism_HermitianCurvature_PrimeToDifferent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:36:17.380943+00:00
-- url     : https://prove2.me/theorems/c7e4aae4-b683-4f3f-a9f1-a2754fc832ce
-- title:
--   Prime To Different
-- statement:
--   Definitions and structural lemmas for Prime To Different, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/PrimeToDifferent.lean

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Definitions.Def_Formalism_HermitianCurvature_StatementI
import Definitions.Def_Formalism_HermitianCurvature_StatementL
import Definitions.Def_Formalism_HermitianCurvature_StatementW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module MeasureTheory
open scoped nonZeroDivisors
section Defs
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
abbrev FI := FractionalIdeal (𝓞 E)⁰ E
noncomputable def deg : ℕ := finrank ℚ (maximalRealSubfield E)
noncomputable def dd : FI E := ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FI E)
def Unram : Prop :=
  differentIdeal ℤ (𝓞 E) =
    (differentIdeal ℤ (𝓞 (maximalRealSubfield E))).map
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))
def UnramAbove (g : ℕ) : Prop :=
  IsCoprime (differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E)) (Ideal.span {(g : 𝓞 E)})
def PrimeToDifferent (g : ℕ) : Prop :=
  IsCoprime (differentIdeal ℤ (𝓞 E)) (Ideal.span {(g : 𝓞 E)})
def SplitsCompletely (p : ℕ) : Prop :=
  p.Prime ∧ ∀ P : Ideal (𝓞 E), P.IsPrime → (p : 𝓞 E) ∈ P →
    Ideal.absNorm P = p ∧ (p : 𝓞 E) ∉ P ^ 2
noncomputable def rd : ℝ := ((|discr E| : ℤ) : ℝ) ^ ((finrank ℚ E : ℝ)⁻¹)
noncomputable def idl (g : ℕ) (k ν : ℤ) : FI E :=
  dd E ^ ν * FractionalIdeal.spanSingleton _ ((g : E) ^ k)
def zsub (A : FI E) : Submodule ℤ E := (A : Submodule (𝓞 E) E).restrictScalars ℤ
noncomputable def conjZ : E →ₗ[ℤ] E :=
  (complexConj E).toAlgHom.toRingHom.toAddMonoidHom.toIntLinearMap
def ConjStable (A : FI E) : Prop := ∀ x ∈ A, complexConj E x ∈ A
noncomputable def twLat (A B : FI E) (s : ℕ) : Submodule ℤ E :=
  zsub E A ⊓ (zsub E B).comap (LinearMap.id - ((-1 : ℤ) ^ s) • conjZ E)
noncomputable def perLat (g : ℕ) (ν : ℤ) (s : ℕ) : Submodule ℤ E :=
  twLat E (idl E g 1 ν) (idl E g 2 ν) s
noncomputable def liftLat (g : ℕ) (ν : ℤ) (s : ℕ) : Submodule ℤ E :=
  twLat E (idl E g (-1) (-ν)) (idl E g 0 (-ν)) s
noncomputable def dualIdl (g : ℕ) (ν : ℤ) : FI E := idl E g (-1) (-(ν + 1))
noncomputable def liftIdl (g : ℕ) (ν : ℤ) : FI E := idl E g (-1) (-ν)
def dualLat (g : ℕ) (L : Submodule ℤ E) : Submodule ℤ E where
  carrier := {x | ∀ y ∈ L, Algebra.trace ℚ E (x * y / g) ∈ (algebraMap ℤ ℚ).range}
  zero_mem' := fun y _ => by simp
  add_mem' := fun {a b} ha hb y hy => by
    have h : (a + b) * y / g = a * y / g + b * y / g := by ring
    rw [h, map_add]
    exact add_mem (ha y hy) (hb y hy)
  smul_mem' := fun n a ha y hy => by
    have h : (n • a) * y / g = n • (a * y / g) := by
      simp only [zsmul_eq_mul]; ring
    rw [h, map_zsmul]
    exact zsmul_mem (ha y hy) n
noncomputable def idx (L M : Submodule ℤ E) : ℕ := L.toAddSubgroup.relIndex M.toAddSubgroup
noncomputable def frameLat (L : Submodule ℤ E) (c : ℝ) :
    Submodule ℤ (mixedEmbedding.mixedSpace E) :=
  (L.map (mixedEmbedding E).toAddMonoidHom.toIntLinearMap).map
    ((c • (LinearMap.id : mixedEmbedding.mixedSpace E →ₗ[ℝ] mixedEmbedding.mixedSpace E)).restrictScalars ℤ)
def locAt (P : Ideal (𝓞 (maximalRealSubfield E))) (L : Submodule ℤ E) : Set E :=
  {t | ∃ a : 𝓞 (maximalRealSubfield E), a ∉ P ∧ algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ L}
def nuBlock (r i s : ℤ) : ℤ := 2 * r + 3 - 2 * i - s
end Defs
section Small
def DegreeFacts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    finrank ℚ E = 2 * deg E ∧ Fintype.card (InfinitePlace E) = deg E ∧ 0 < deg E
def PowConjStable : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (k ν : ℤ),
    ConjStable E (idl E g k ν)
def UnramRelative : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unram E →
    differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ ∧ ∀ g : ℕ, UnramAbove E g
def DiscrSquare : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unram E →
    (discr E).natAbs = (discr (maximalRealSubfield E)).natAbs ^ 2
def SplitCoprime : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (p : ℕ),
    SplitsCompletely E p → PrimeToDifferent E p
def Between : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A B : FI E) (s : ℕ),
    B ≤ A → ConjStable E B → zsub E B ≤ twLat E A B s ∧ twLat E A B s ≤ zsub E A
def IndexCore : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : FI E) (g s : ℕ),
    A ≠ 0 → ConjStable E A → 0 < g → UnramAbove E g →
    idx E (twLat E A (A * FractionalIdeal.spanSingleton _ (g : E)) s) (zsub E A) = g ^ deg E ∧
    idx E (zsub E (A * FractionalIdeal.spanSingleton _ (g : E)))
      (twLat E A (A * FractionalIdeal.spanSingleton _ (g : E)) s) = g ^ deg E
def DualSubset : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (ν : ℤ) (s : ℕ), 0 < g →
    dualLat E g (perLat E g ν s) ≤ twLat E (dualIdl E g ν) (idl E g 0 (-(ν + 1))) (s + 1)
def DualSupset : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unram E →
    ∀ (g : ℕ) (ν : ℤ) (s : ℕ), 0 < g →
      twLat E (dualIdl E g ν) (idl E g 0 (-(ν + 1))) (s + 1) ≤ dualLat E g (perLat E g ν s)
def NormIdl : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (k ν : ℤ), 0 < g →
    √(FractionalIdeal.absNorm (idl E g k ν) : ℝ) = ((g : ℝ) ^ k * rd E ^ ν) ^ deg E
open scoped Classical in

def CovolumeIndex : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : FI E) (L : Submodule ℤ E) (c : ℝ),
    B ≠ 0 → c ≠ 0 → zsub E B ≤ L → idx E (zsub E B) L ≠ 0 →
    DiscreteTopology (frameLat E L c) ∧
    Submodule.span ℝ (frameLat E L c : Set (mixedEmbedding.mixedSpace E)) = ⊤ ∧
    ZLattice.covolume (E := mixedEmbedding.mixedSpace E) (frameLat E L c) =
      |c| ^ (2 * deg E) * (FractionalIdeal.absNorm B : ℝ) * (2⁻¹ : ℝ) ^ deg E *
        √((|discr E| : ℤ) : ℝ) / (idx E (zsub E B) L : ℝ)
def IdealsMatch : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (r i s : ℤ),
    dualIdl E g (nuBlock r i s) = liftIdl E g (nuBlock r i (s - 1)) ∧
    dualIdl E g (nuBlock r i s) = idl E g (-1) (-(2 * r + 4 - 2 * i - s)) ∧
    nuBlock r i s = 2 * (r + 1) - i - (i - 1 + s)
def LocTw : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A B : FI E) (s : ℕ)
    (P : Ideal (𝓞 (maximalRealSubfield E))), P.IsPrime → ∀ t : E,
    (t ∈ locAt E P (twLat E A B s) ↔
      t ∈ locAt E P (zsub E A) ∧ t - (-1) ^ s * complexConj E t ∈ locAt E P (zsub E B))
def LocOrdinary : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (k ν : ℤ)
    (P : Ideal (𝓞 (maximalRealSubfield E))), P.IsPrime → (g : 𝓞 (maximalRealSubfield E)) ∉ P →
    locAt E P (zsub E (idl E g k ν)) = locAt E P (zsub E (idl E g 0 ν))
def LocTyped : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (k ν : ℤ), 0 < g →
    PrimeToDifferent E g →
    ∀ P : Ideal (𝓞 (maximalRealSubfield E)), P.IsPrime → (g : 𝓞 (maximalRealSubfield E)) ∈ P →
    locAt E P (zsub E (idl E g k ν)) = locAt E P (zsub E (idl E g k 0))
def IsFLattice (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule ℤ E) : Prop :=
  (∀ (a : 𝓞 (maximalRealSubfield E)) (t : E), t ∈ L →
    algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ L) ∧
  ∀ t : E, ∃ n : ℕ, 0 < n ∧ (n : E) * t ∈ L
def QuotientSplits (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule ℤ E) : Prop :=
  (∀ t : E, {P : Ideal (𝓞 (maximalRealSubfield E)) | P.IsMaximal ∧ t ∉ locAt E P L}.Finite) ∧
  (∀ t : E, (∀ P : Ideal (𝓞 (maximalRealSubfield E)), P.IsMaximal → t ∈ locAt E P L) → t ∈ L) ∧
  ∀ (S : Finset (Ideal (𝓞 (maximalRealSubfield E)))) (τ : Ideal (𝓞 (maximalRealSubfield E)) → E),
    (∀ P ∈ S, P.IsMaximal) →
    ∃ t : E, (∀ P ∈ S, t - τ P ∈ locAt E P L) ∧
      ∀ P : Ideal (𝓞 (maximalRealSubfield E)), P.IsMaximal → P ∉ S → t ∈ locAt E P L
def TwIsFLattice : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A B : FI E) (s : ℕ),
    B ≠ 0 → B ≤ A → ConjStable E B → IsFLattice E (twLat E A B s)
def LocalGlobal : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule ℤ E),
    IsFLattice E L → QuotientSplits E L
end Small
section Text
open scoped Classical in

def LatticeFacts (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (ν : ℤ) (s : ℕ) :
    Prop :=
  zsub E (idl E g 2 ν) ≤ perLat E g ν s ∧
  perLat E g ν s ≤ zsub E (idl E g 1 ν) ∧
  idx E (perLat E g ν s) (zsub E (idl E g 1 ν)) = g ^ deg E ∧
  idx E (zsub E (idl E g 2 ν)) (perLat E g ν s) = g ^ deg E ∧
  dualLat E g (perLat E g ν s) ≤ zsub E (dualIdl E g ν) ∧
  idx E (dualLat E g (perLat E g ν s)) (zsub E (dualIdl E g ν)) = g ^ deg E ∧
  liftLat E g ν s ≤ zsub E (liftIdl E g ν) ∧
  idx E (liftLat E g ν s) (zsub E (liftIdl E g ν)) = g ^ deg E ∧
  √(FractionalIdeal.absNorm (dualIdl E g ν) : ℝ) = ((g : ℝ) * rd E ^ (ν + 1)) ^ (-(deg E : ℤ)) ∧
  DiscreteTopology (frameLat E (perLat E g ν s) (rd E ^ (-ν))) ∧
  Submodule.span ℝ
    (frameLat E (perLat E g ν s) (rd E ^ (-ν)) : Set (mixedEmbedding.mixedSpace E)) = ⊤ ∧
  ZLattice.covolume (E := mixedEmbedding.mixedSpace E) (frameLat E (perLat E g ν s) (rd E ^ (-ν))) =
    (rd E / 2) ^ deg E * (g : ℝ) ^ (3 * deg E)
def LatticesGeneral : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unram E →
    ∀ (g : ℕ) (ν : ℤ) (s : ℕ), 0 < g → LatticeFacts E g ν s
def TextLattices : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unram E →
    ∀ g₁ g₂ : ℕ, SplitsCompletely E g₁ → SplitsCompletely E g₂ →
    ∀ (ν : ℤ) (s : ℕ), 1 ≤ s → LatticeFacts E (g₁ * g₂) ν s
def AssembleLattices : Prop :=
  DegreeFacts → PowConjStable → UnramRelative → Between → IndexCore →
    DualSubset → DualSupset → NormIdl → CovolumeIndex → LatticesGeneral
def TextFromGeneral : Prop := LatticesGeneral → TextLattices
def LeastNorm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (ν : ℤ) (s : ℕ), 0 < g →
    ∀ l ∈ dualLat E g (perLat E g ν s), l ≠ 0 →
      ((g : ℝ) * rd E ^ (ν + 1)) ^ (-(deg E : ℤ)) ≤ ∏ w : InfinitePlace E, w l
def SizeQuotient : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g r i : ℕ) (c : InfinitePlace E → ℝ),
    0 < g → (∀ v, 0 ≤ c v) →
    ∀ l ∈ dualLat E g (perLat E g (nuBlock r i 1) 1), l ≠ 0 →
      (∏ v, c v * (2 * Real.pi / g) ^ ((2 * i : ℤ) - 3 - 2 * r)) / ∏ w : InfinitePlace E, w l ≤
        (∏ v, c v) * (2 * Real.pi / rd E) ^ (((2 * i : ℤ) - 3 - 2 * r) * deg E) *
          (g : ℝ) ^ (((2 * r + 2 : ℤ) - 2 * ((i : ℤ) - 1)) * deg E)
def TextLeast : Prop := LeastNorm ∧ SizeQuotient
def AssembleLeast : Prop :=
  Formalism.FourierDecayAlt.L.DualLatticeInclusion → Formalism.FourierDecayAlt.W.NormLower → Formalism.FourierDecayAlt.DualSizeIdentity → DegreeFacts →
    PowConjStable → Between → NormIdl → TextLeast
def TextLocal : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g₁ g₂ : ℕ),
    SplitsCompletely E g₁ → SplitsCompletely E g₂ → ∀ (ν : ℤ) (s : ℕ), 1 ≤ s →
    (∀ P : Ideal (𝓞 (maximalRealSubfield E)), P.IsMaximal →
      ((g₁ * g₂ : ℕ) : 𝓞 (maximalRealSubfield E)) ∉ P →
      locAt E P (perLat E (g₁ * g₂) ν s) = locAt E P (zsub E (idl E (g₁ * g₂) 0 ν))) ∧
    (∀ P : Ideal (𝓞 (maximalRealSubfield E)), P.IsMaximal →
      ((g₁ * g₂ : ℕ) : 𝓞 (maximalRealSubfield E)) ∈ P → ∀ t : E,
      (t ∈ locAt E P (perLat E (g₁ * g₂) ν s) ↔
        t ∈ locAt E P (zsub E (idl E (g₁ * g₂) 1 0)) ∧
          t - (-1) ^ s * complexConj E t ∈ locAt E P (zsub E (idl E (g₁ * g₂) 2 0)))) ∧
    QuotientSplits E (perLat E (g₁ * g₂) ν s)
def AssembleLocal : Prop :=
  PowConjStable → SplitCoprime → LocTw → LocOrdinary → LocTyped → TwIsFLattice → LocalGlobal →
    TextLocal
def TypedModel : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (ν : ℤ) (s : ℕ), 0 < g →
    PrimeToDifferent E g →
    ∀ P : Ideal (𝓞 (maximalRealSubfield E)), P.IsPrime → (g : 𝓞 (maximalRealSubfield E)) ∈ P →
    ∀ (K : Type) [Field K] (o : Subring K) (σ : E →+* K),
      (∀ x : E, x ∈ locAt E P (zsub E 1) ↔ σ x ∈ o ∧ σ (complexConj E x) ∈ o) →
      ∀ t : E, (t ∈ locAt E P (perLat E g ν s) ↔
        (σ t / (g : K), (-1) ^ s * σ (complexConj E t) / (g : K)) ∈ Formalism.FourierDecayAlt.I.orderR o (g : K))
end Text
end Formalism.FourierDecayAlt.S6


