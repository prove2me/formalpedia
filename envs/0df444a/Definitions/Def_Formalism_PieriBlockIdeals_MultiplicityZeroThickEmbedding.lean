-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
-- name    : Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:11.478105+00:00
-- url     : https://prove2.me/theorems/799411a3-3a8c-4159-a296-4aa31c829ab1
-- title:
--   Multiplicity Zero Thick Embedding
-- statement:
--   Definitions and structural lemmas for Multiplicity Zero Thick Embedding, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/MultiplicityZeroThickEmbedding.lean

import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace Formalism.CohomologicalDescent.WorkedExample
open Formalism.CohomologicalDescent
def ReflIdentity : Prop :=
  ∀ (n i : ℕ) (μ : ℤ),
    ((n : ℚ) - 1) / 2 - ((μ : ℚ) + (((n : ℚ) + 1) / 2 - (i : ℚ))) =
        ((((n : ℤ) - 1) - (μ + (n : ℤ) - (i : ℤ)) : ℤ) : ℚ) ∧
      ((n : ℚ) - 1) / 2 - (-((μ : ℚ) + (((n : ℚ) + 1) / 2 - (i : ℚ)))) =
        ((μ + (n : ℤ) - (i : ℤ) : ℤ) : ℚ)
def FlipSets : Prop :=
  ∀ (l : ℕ) (b h : ℤ) (t κ : ℕ),
    (Finset.Icc b (b + t - 1)).image (fun u => h - u) =
        Finset.Icc (h - (b + t - 1)) (h - (b + t - 1) + t - 1) ∧
      (Finset.Icc (b - κ) (b + t - 1 + κ)).image (fun u => h - u) =
        Finset.Icc (h - (b + t - 1) - κ) (h - (b + t - 1) + t - 1 + κ) ∧
      ∀ x u : ℤ, h - x ≡ h - u [ZMOD (l : ℤ)] ↔ x ≡ u [ZMOD (l : ℤ)]
def MwFlip : Prop :=
  ∀ (l : ℕ) (b h : ℤ) (t κ : ℕ) (U : Finset ℤ),
    mwCount l (h - (b + t - 1)) t κ (U.image fun u => h - u) = mwCount l b t κ U
def LinkageFlip : Prop :=
  ∀ (K : Type) [CommRing K] (N : ℕ) (U U' : Fin N → ℤ) (c c' h : ℤ),
    (∏ a, (Polynomial.X + Polynomial.C (((U a + c : ℤ)) : K))) =
      ∏ a, (Polynomial.X + Polynomial.C (((U' a + c : ℤ)) : K)) →
    (∏ a, (Polynomial.X + Polynomial.C (((h - U a + c' : ℤ)) : K))) =
      ∏ a, (Polynomial.X + Polynomial.C (((h - U' a + c' : ℤ)) : K))
def ResidueFlip : Prop :=
  ∀ (l N : ℕ) (U U' : Fin N → ℤ) (h : ℤ),
    Multiset.map (fun a => ((U a : ℤ) : ZMod l)) Finset.univ.val =
      Multiset.map (fun a => ((U' a : ℤ) : ZMod l)) Finset.univ.val →
    Multiset.map (fun a => ((h - U a : ℤ) : ZMod l)) Finset.univ.val =
      Multiset.map (fun a => ((h - U' a : ℤ) : ZMod l)) Finset.univ.val
structure Labels (ι : Type) (N : ℕ) where
  cc : ι → ι
  Φ : Set ι
  U : ι → Fin N → ℤ
  U' : ι → Fin N → ℤ
  bot : ι → ℤ
namespace Labels
variable {ι : Type} {N : ℕ}
def Refl (D : Labels ι N) (σ : Equiv.Perm ι) (h t : ℕ) : Prop :=
  (∀ i, D.cc (D.cc i) = i) ∧ (∀ i, σ (D.cc i) = D.cc (σ i)) ∧ (∀ i, i ∈ D.Φ ∨ D.cc i ∈ D.Φ) ∧
  (∀ i a, D.U (D.cc i) a = (h : ℤ) - D.U i (Fin.rev a)) ∧
  (∀ i a, D.U' (D.cc i) a = (h : ℤ) - D.U' i (Fin.rev a)) ∧
  (∀ i, D.bot (D.cc i) = (h : ℤ) - (D.bot i + (t : ℤ) - 1))
def Linked (D : Labels ι N) (F : Type) [Field F] (t : ℕ) (cst : ι → ℤ) : Prop :=
  ∀ i ∈ D.Φ, StrictAnti (D.U i) ∧ StrictAnti (D.U' i) ∧
    (∀ s : Fin t, ∃ a, D.U i a = D.bot i + ((s : ℕ) : ℤ)) ∧
    (∏ a, (Polynomial.X + Polynomial.C (((D.U i a + cst i : ℤ)) : F))) =
      ∏ a, (Polynomial.X + Polynomial.C (((D.U' i a + cst i : ℤ)) : F))
def Carried (D : Labels ι N) (ep : ι → ι) (J : ι → Fin N → ℤ) (botJ : ι → ℤ) : Prop :=
  (ep = id ∨ ep = D.cc) ∧ (∀ i, J (ep i) = D.U' i) ∧ (∀ i, botJ (ep i) = D.bot i)
def mw (D : Labels ι N) (l t κ : ℕ) (i : ι) : ℕ :=
  mwCount l (D.bot i) t κ (Finset.univ.image (D.U i))
end Labels
def ShapeAt {ι : Type} (k j t q : ℕ) (D : Labels ι (k + j + t + q)) (τ : ι) : Prop :=
  (∀ a, 0 ≤ D.U τ a) ∧ ∑ a, D.U τ a = ∑ a, D.U' τ a ∧
  ∀ a : Fin (k + j + t + q), k + j ≤ (a : ℕ) → (a : ℕ) < k + j + t →
    D.U τ a = D.bot τ + ((k + j + t - 1 - (a : ℕ) : ℕ) : ℤ)
def DepthBound {ι : Type} (k j t q l h : ℕ) (D : Labels ι (k + j + t + q)) (σ : Equiv.Perm ι)
    (τ : ι) : Prop :=
  ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < k + j),
      (D.U τ a - D.U' τ a) ≤
    (q : ℤ) * h +
      ((l : ℤ) * (D.mw l t (h / (l - 1)) (σ τ) : ℤ) + (D.mw l t (h / (l - 1)) τ : ℤ)) *
        ((t : ℤ) + 2 * ((h / (l - 1) : ℕ) : ℤ))
def MwLetters : Prop :=
  ∀ (ι : Type) (N : ℕ) (D : Labels ι N) (σ : Equiv.Perm ι) (h t : ℕ), D.Refl σ h t →
    ∀ (l κ : ℕ) (i : ι), D.mw l t κ (D.cc i) = D.mw l t κ i
def LinkedAll : Prop :=
  ∀ (ι : Type) (N : ℕ) (D : Labels ι N) (σ : Equiv.Perm ι) (h t : ℕ) (F : Type) [Field F]
    (cst : ι → ℤ), D.Refl σ h t → D.Linked F t cst →
    ∀ i, StrictAnti (D.U i) ∧ StrictAnti (D.U' i) ∧
      (∀ s : Fin t, ∃ a, D.U i a = D.bot i + ((s : ℕ) : ℤ)) ∧
      (∏ a, (Polynomial.X + Polynomial.C (((D.U i a + 0 : ℤ)) : F))) =
        ∏ a, (Polynomial.X + Polynomial.C (((D.U' i a + 0 : ℤ)) : F))
def WEOrient : Prop :=
  ∀ (ι : Type) [Fintype ι] (σ : Equiv.Perm ι) (k j t q l h : ℕ) (F : Type) [Field F] [CharP F l]
    (W : WData ι t (k + j + t + q) F) (D : Labels ι (k + j + t + q)) (cst : ι → ℤ)
    (ep : ι → ι) (J : ι → Fin (k + j + t + q) → ℤ) (botJ : ι → ℤ)
    (kap : ι → Fin t → ℤ) (c : ι → ℕ) (τ : ι),
    l.Prime → t + 2 * (h / (l - 1)) < l →
    D.Refl σ h t → D.Linked F t cst → D.Carried ep J botJ →
    WProps W σ l J botJ kap c →
    (∀ i (s : Fin t), 0 ≤ botJ i + ((s : ℕ) : ℤ) ∧ botJ i + ((s : ℕ) : ℤ) ≤ (h : ℤ)) →
    (∀ i (s : Fin t), 0 ≤ (l : ℤ) * kap (σ i) s + (botJ i + ((s : ℕ) : ℤ)) - kap i s ∧
      (l : ℤ) * kap (σ i) s + (botJ i + ((s : ℕ) : ℤ)) - kap i s ≤ (h : ℤ)) →
    ShapeAt k j t q D τ → (∀ a, 0 ≤ D.U' τ a ∧ D.U' τ a ≤ (h : ℤ)) →
    (c (ep τ) : ℤ) = ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => k + j + q ≤ (a : ℕ)),
      D.U' τ a →
    DepthBound k j t q l h D σ τ
def WEOrientInputs : Prop :=
  ∀ (ι : Type) [Fintype ι] (σ : Equiv.Perm ι) (k j t q l h : ℕ) [Fact l.Prime] (O F : Type)
    [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [Field F] [CharP F l]
    (W : FrobeniusPeriodChange.WLat ι t (k + j + t + q) O F) (u : ℤ_[l]ˣ) (c : ℤ_[l])
    (D : Labels ι (k + j + t + q)) (cst : ι → ℤ)
    (ep : ι → ι) (J : ι → Fin (k + j + t + q) → ℤ) (botJ : ι → ℤ) (kap : ι → Fin t → ℤ) (τ : ι),
    l ≠ 2 → t + 2 * (h / (l - 1)) < l →
    D.Refl σ h t → D.Linked F t cst → D.Carried ep J botJ →
    FrobeniusPeriodChange.WInputs W σ l h u c J (fun i s => botJ i + ((s : ℕ) : ℤ)) kap →
    ShapeAt k j t q D τ →
    DepthBound k j t q l h D σ τ
def WEOrientLattice : Prop :=
  ∀ (ι : Type) [Fintype ι] (σ : Equiv.Perm ι) (k j t q l h : ℕ) [Fact l.Prime] (O F L : Type)
    [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [Field F] [CharP F l] [Field L] (I : Ideal O)
    [IsAdicComplete I O] (W : FrobeniusPeriodChange.WLat ι t (k + j + t + q) O F) (u : ℤ_[l]ˣ) (c : ℤ_[l])
    (D : Labels ι (k + j + t + q)) (cst : ι → ℤ)
    (ep : ι → ι) (J : ι → Fin (k + j + t + q) → ℤ) (botJ : ι → ℤ) (kap : ι → Fin t → ℤ) (τ : ι)
    (ζ : O) (em : O →+* L) (jj : ℕ → PowerSeries O →+* PowerSeries L),
    l ≠ 2 → t + 2 * (h / (l - 1)) < l →
    D.Refl σ h t → D.Linked F t cst → D.Carried ep J botJ →
    FrobeniusPeriodChange.NInputs W σ l h u c J (fun i s => botJ i + ((s : ℕ) : ℤ)) kap I ζ em jj →
    ShapeAt k j t q D τ →
    DepthBound k j t q l h D σ τ
def WEArithReflected : Prop :=
  ∀ (k j t q l h κ mw mwp : ℕ) (U U' : Fin (k + j + t + q) → ℤ) (kc kp : ℤ),
    StrictAnti U → StrictAnti U' → (∀ a, U a ≤ (h : ℤ)) → (∀ a, 0 ≤ U' a) →
    ∑ a, U a = ∑ a, U' a →
    ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < t), ((h : ℤ) - U' a) ≤
      (∑ a ∈ Finset.univ.filter
        (fun a : Fin (k + j + t + q) => k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + t), ((h : ℤ) - U a)) +
        (l : ℤ) * kp - kc →
    |kc| ≤ (mw : ℤ) * ((t : ℤ) + 2 * κ) → |kp| ≤ (mwp : ℤ) * ((t : ℤ) + 2 * κ) →
    ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => k + j + t ≤ (a : ℕ)), (U' a - U a) ≤
      ((k : ℤ) + j) * h + ((l : ℤ) * mwp + mw) * ((t : ℤ) + 2 * κ)
def rho (n : ℕ) (a : Fin n) : ℝ := ((n : ℝ) + 1 - 2 * (((a : ℕ) : ℝ) + 1)) / 2
def aPlus (p q' t : ℕ) (v : Fin p → ℝ) (e : ℝ) (i : Fin p) : ℝ :=
  (v i + e) - (((p : ℝ) + q' + t) + 1 - 2 * (((i : ℕ) : ℝ) + 1)) / 2 - ((p : ℝ) - q') / 2
def aMinus (q' t : ℕ) (β : Fin q' → ℝ) (e : ℝ) (d : Fin q') : ℝ :=
  (β (Fin.rev d) - e) + (1 - (t : ℝ) - 2 * ((((Fin.rev d : Fin q') : ℕ) : ℝ) + 1)) / 2
def twistedSequenceWeight (p q' t : ℕ) (v : Fin p → ℝ) (β : Fin q' → ℝ) (e : ℝ) (i : Fin (p + t + q')) : ℝ :=
  Fin.append (Fin.append (aPlus p q' t v e) (fun _ : Fin t => (0 : ℝ)))
      (fun c : Fin q' => -aMinus q' t β e (Fin.rev c)) i + ((p : ℝ) - q') / 2 - e
def exampleParameterVector (p q' t : ℕ) (v : Fin p → ℝ) (β : Fin q' → ℝ) (e : ℝ) : Fin (p + t + q') → ℝ :=
  Fin.append (Fin.append v (fun a : Fin t => -e + ((t : ℝ) + 1 - 2 * (((a : ℕ) : ℝ) + 1)) / 2))
    (fun c : Fin q' => -β c)
def WeightAddRhoEqParameter : Prop :=
  ∀ (p q' t : ℕ) (v : Fin p → ℝ) (β : Fin q' → ℝ) (e : ℝ) (i : Fin (p + t + q')),
    twistedSequenceWeight p q' t v β e i + rho (p + t + q') i = exampleParameterVector p q' t v β e i
def ParameterSequenceCentred : Prop :=
  ∀ (p q' t : ℕ) (v : Fin p → ℝ) (β : Fin q' → ℝ) (e : ℝ) (a : Fin t),
    exampleParameterVector p q' t v β e (Fin.castAdd q' (Fin.natAdd p a)) =
        -e + ((t : ℝ) - 1) / 2 - ((a : ℕ) : ℝ) ∧
      exampleParameterVector p q' t v β e (Fin.castAdd q' (Fin.natAdd p a)) +
        exampleParameterVector p q' t v β e (Fin.castAdd q' (Fin.natAdd p (Fin.rev a))) = 2 * -e
def ParameterStrictOrder : Prop :=
  ∀ (p q' t : ℕ) (v : Fin p → ℝ) (β : Fin q' → ℝ) (e : ℝ), StrictAnti v → StrictMono β →
    (∀ i, -e + ((t : ℝ) - 1) / 2 < v i) → (∀ c, -β c < -e - ((t : ℝ) - 1) / 2) →
    (∀ i c, -β c < v i) →
    StrictAnti (exampleParameterVector p q' t v β e)
def ParameterShapeBounds : Prop :=
  ∀ (P : LogSmallConstantBounds.Par) (kc j q' : ℕ) (cloud : Fin kc → ℝ) (bu : Fin j → ℝ) (bd : Fin q' → ℝ)
    (e c : ℝ) (σ : ℤ) (z : Fin (kc + j + P.t + q') → ℤ) (bot : ℤ),
    (σ = 1 ∨ σ = -1) →
    (∀ i, 0 ≤ cloud i ∧ cloud i ≤ P.S) →
    (∀ i, 2 * P.b / P.lstar + (P.t : ℝ) / 2 + 3 ≤ |bu i - e| ∧ |bu i - e| ≤ P.η) →
    (∀ i, 2 * P.b / P.lstar + (P.t : ℝ) / 2 + 3 ≤ |bd i - e| ∧ |bd i - e| ≤ P.η) →
    (∀ a, (z a : ℝ) = c + (σ : ℝ) *
      (twistedSequenceWeight (kc + j) q' P.t (Fin.append cloud fun i => -bu i) bd e a +
        rho (kc + j + P.t + q') a)) →
    IsLeast (Set.range fun s : Fin P.t => z (Fin.castAdd q' (Fin.natAdd (kc + j) s))) bot →
    P.Shape (Finset.univ.image z) bot c e σ
def MultiplicityZeroThickEmbedding : Prop :=
  ∀ (P : LogSmallConstantBounds.Par), P.Hyp → P.Large → ∀ l : ℕ, l.Prime → P.lJ < (l : ℝ) →
    ∀ (kc j q' : ℕ) (cloud : Fin kc → ℝ) (bu : Fin j → ℝ) (bd : Fin q' → ℝ)
    (e c : ℝ) (σ : ℤ) (z : Fin (kc + j + P.t + q') → ℤ) (bot : ℤ),
    (σ = 1 ∨ σ = -1) →
    (∀ i, 0 ≤ cloud i ∧ cloud i ≤ P.S) →
    (∀ i, 2 * P.b / P.lstar + (P.t : ℝ) / 2 + 3 ≤ |bu i - e| ∧ |bu i - e| ≤ P.η) →
    (∀ i, 2 * P.b / P.lstar + (P.t : ℝ) / 2 + 3 ≤ |bd i - e| ∧ |bd i - e| ≤ P.η) →
    (∀ a, (z a : ℝ) = c + (σ : ℝ) *
      (twistedSequenceWeight (kc + j) q' P.t (Fin.append cloud fun i => -bu i) bd e a +
        rho (kc + j + P.t + q') a)) →
    IsLeast (Set.range fun s : Fin P.t => z (Fin.castAdd q' (Fin.natAdd (kc + j) s))) bot →
    ((P.Thick e ∧ ¬ P.Excl l) ∨ P.Top e ∨ P.Thin e) →
    mwCount l bot P.t (P.kap l) (Finset.univ.image z) = 0
def ShapeDisp (P : LogSmallConstantBounds.Par) (U : Finset ℤ) (bot : ℤ) (c e δ : ℝ) (σ : ℤ) : Prop :=
  (σ = 1 ∨ σ = -1) ∧ (σ : ℝ) * ((bot : ℝ) + ((P.t : ℝ) - 1) / 2 - c) = -e + δ ∧
    ∀ u ∈ U, u ∉ Finset.Icc bot (bot + (P.t : ℤ) - 1) →
      (0 ≤ (σ : ℝ) * ((u : ℝ) - c) ∧ (σ : ℝ) * ((u : ℝ) - c) ≤ P.S) ∨
      (2 * P.b / P.lstar + (P.t : ℝ) / 2 + 3 ≤ |(σ : ℝ) * ((u : ℝ) - c) + e| ∧
        |(σ : ℝ) * ((u : ℝ) - c) + e| ≤ P.η)
def SlackSize : Prop :=
  ∀ P : LogSmallConstantBounds.Par, P.Hyp → P.Large →
    48 * (P.t : ℝ) ^ 2 ≤ P.b / P.lstar ∧
      ∀ l : ℕ, P.lJ < (l : ℝ) → (P.kap l : ℝ) ≤ 2 / 3 * (P.b / P.lstar)
def NoResDisplaced : Prop :=
  ∀ P : LogSmallConstantBounds.Par, P.Hyp → P.Large → ∀ l : ℕ, l.Prime → P.lJ < (l : ℝ) →
    ∀ (U : Finset ℤ) (bot : ℤ) (c e δ : ℝ) (σ : ℤ), |δ| ≤ P.b / P.lstar →
      ShapeDisp P U bot c e δ σ →
      ((P.Thick e ∧ ¬ P.Excl l) ∨ P.Top e ∨ P.Thin e) →
      mwCount l bot P.t (P.kap l) U = 0
def LstarGapInequalities : Prop :=
  ∀ P : LogSmallConstantBounds.Par, P.Hyp → P.Large →
    P.S + P.η + P.b / P.lstar < P.lstar ∧ (P.t : ℝ) + P.b / P.lstar < P.lstar ∧
      P.S + P.η + (P.t : ℝ) + 2 * P.b / P.lstar < 2 * P.lstar ∧ 2 * P.lstar ≤ P.b ∧
      P.S + P.η + (P.t : ℝ) + 2 * P.b / P.lstar ≤ P.b
def ParameterQuotientBoundOfTwoLeF : Prop :=
  ∀ P : LogSmallConstantBounds.Par, P.Hyp → 2 ≤ P.f → 0 ≤ P.L →
    6 ≤ P.t ∧ 12 ≤ P.t * P.f * P.k ^ 3 * P.m ∧
    ∀ η' : ℝ, 0 ≤ η' → η' ≤ 3 * P.η →
      η' * (P.Nr : ℝ) ^ 2 * P.L ≤ 3 * P.η * (4 * (P.t : ℝ) ^ 2) * P.L ∧
      3 * P.η * (4 * (P.t : ℝ) ^ 2) * P.L ≤
        12 * P.L * P.b / ((P.t : ℝ) * (P.f : ℝ) * (P.k : ℝ) ^ 3) ∧
      12 * P.L * P.b / ((P.t : ℝ) * (P.f : ℝ) * (P.k : ℝ) ^ 3) ≤ (P.m : ℝ) * P.b * P.L
def ParameterQuotientBoundFailsAtFEqOne : Prop :=
  ∃ P : LogSmallConstantBounds.Par, P.Hyp ∧ P.Large ∧ P.f = 1 ∧ P.t * P.f * P.k ^ 3 * P.m < 12 ∧
    (P.m : ℝ) * P.b * P.L < 12 * P.L * P.b / ((P.t : ℝ) * (P.f : ℝ) * (P.k : ℝ) ^ 3)
def TermCSmall : Prop :=
  ∀ P : LogSmallConstantBounds.Par, P.Hyp → P.Large → 2 ≤ P.f → ∀ (ι : Type) (D : LogSmallConstantBounds.SizeData₂ ι), D.ThickA P →
    ∀ τ ∈ D.T2, ∀ l : ℕ, l.Prime → (l : ℝ) < 2 * P.η + (P.t : ℝ) →
      (D.ex τ l : ℝ) * Real.log (l : ℝ) ≤ (P.m : ℝ) * P.b * P.L / (l : ℝ)
end Formalism.CohomologicalDescent.WorkedExample


