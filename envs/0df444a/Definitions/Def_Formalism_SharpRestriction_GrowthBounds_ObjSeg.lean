-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjSeg
-- name    : Formalism_SharpRestriction_GrowthBounds_ObjSeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:34:55.262896+00:00
-- url     : https://prove2.me/theorems/b4409cab-6fb7-4692-945a-4e8c7f30c17a
-- title:
--   Obj Seg
-- statement:
--   Definitions and structural lemmas for Obj Seg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ObjSeg.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.MainNotions.G
structure ChainLetters (N : ℕ) where
  vec : Fin N → Bool
  deg : Fin N → ℕ
def chPol (K : Type*) [CommSemiring K] (r : ℕ) {N : ℕ} (LL : ChainLetters N) :
    Submodule K (MvPolynomial (Fin N × Fin r) K) :=
  Pol K r LL.deg
def chWt {N r : ℕ} (LL : ChainLetters N) (j : ℕ) (c : Fin r) (m : Fin N × Fin r →₀ ℕ) : ℤ :=
  ∑ i : Fin N, if (i : ℕ) < j then (if LL.vec i then (m (i, c) : ℤ) else -(m (i, c) : ℤ)) else 0
def chStable (K : Type*) [CommRing K] {N r : ℕ} (LL : ChainLetters N) (j : ℕ)
    (S : Submodule K (MvPolynomial (Fin N × Fin r) K)) : Prop :=
  ∀ c d : Fin r, ∀ x ∈ S, glAct K (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} c d x ∈ S
def YCond (K : Type*) [CommRing K] {N r : ℕ} [NeZero r] (LL : ChainLetters N) (j : ℕ) (M : WithTop ℤ) :
    Submodule K (MvPolynomial (Fin N × Fin r) K) :=
  sSup {S | S ≤ MvPolynomial.restrictSupport K {m | ((chWt LL j 0 m : ℤ) : WithTop ℤ) ≤ M} ∧
    chStable K LL j S}
def Yjt (K : Type*) [CommRing K] {N r : ℕ} [NeZero r] (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) : Submodule K (MvPolynomial (Fin N × Fin r) K) :=
  chPol K r LL ⊓ ⨅ k, YCond K LL (J k) (M k)
def YjtZ (O : Type*) [CommRing O] [IsDomain O] {N r : ℕ} [NeZero r] (LL : ChainLetters N) {q : ℕ}
    (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) : Submodule O (MvPolynomial (Fin N × Fin r) (KK O)) :=
  (Yjt (KK O) LL J M).restrictScalars O ⊓ IntPol O (Fin N × Fin r)
structure TieData where
  t : ℕ
  pos : Fin t → ℕ
  z : Fin t → ℕ
  q : ℕ
  J : Fin q → ℕ
  thr : Fin q → WithTop ℤ
abbrev BVar (N r t : ℕ) := (Fin (N + 1) × Fin r) ⊕ (Fin (t + 1) × Bool)
structure BlockData (N : ℕ) where
  LL : ChainLetters N
  T : TieData
  uPos : Fin N
  B : ℕ
  zPlus : ℕ
variable {N r : ℕ}
def finPos (N : ℕ) (k : ℕ) : Fin (N + 1) := ⟨min k N, Nat.lt_succ_of_le (min_le_right k N)⟩
def BlockData.lettersAt (D : BlockData N) (j : Fin D.T.t → ℕ) (jp : ℕ) : ChainLetters N where
  vec := D.LL.vec
  deg := fun a => D.LL.deg a - (∑ i, if (a : ℕ) = D.T.pos i ∨ (a : ℕ) = D.T.pos i + 1 then j i else 0) -
    (if a = D.uPos then jp else 0)
def chainEmb (N r t : ℕ) : Fin N × Fin r → BVar N r t := fun x => Sum.inl (Fin.castSucc x.1, x.2)
def xiVar (N r t : ℕ) (c : Fin r) : BVar N r t := Sum.inl (Fin.last N, c)
def scalZ (N r t : ℕ) (i : Fin (t + 1)) : BVar N r t := Sum.inr (i, false)
def scalS (N r t : ℕ) (i : Fin (t + 1)) : BVar N r t := Sum.inr (i, true)
def BlockData.Ehat (O : Type*) [CommRing O] [IsDomain O] (D : BlockData N) (i : Fin D.T.t) :
    MvPolynomial (BVar N r D.T.t) (KK O) :=
  X (scalZ N r D.T.t (Fin.castSucc i)) * X (scalS N r D.T.t (Fin.castSucc i)) +
    ∑ c, X (Sum.inl (finPos N (D.T.pos i), c)) * X (Sum.inl (finPos N (D.T.pos i + 1), c))
def BlockData.Eplus (O : Type*) [CommRing O] [IsDomain O] (D : BlockData N) :
    MvPolynomial (BVar N r D.T.t) (KK O) :=
  X (scalZ N r D.T.t (Fin.last D.T.t)) * X (scalS N r D.T.t (Fin.last D.T.t)) +
    ∑ c, X (Sum.inl (Fin.castSucc D.uPos, c)) * X (xiVar N r D.T.t c)
def XiPolZ (O : Type*) [CommRing O] [IsDomain O] (N r t b : ℕ) :
    Submodule O (MvPolynomial (BVar N r t) (KK O)) :=
  (MvPolynomial.restrictSupport (KK O)
      {m | (∀ v ∈ m.support, ∃ c, v = xiVar N r t c) ∧ ∑ c, m (xiVar N r t c) = b}).restrictScalars O ⊓
    IntPol O (BVar N r t)
def BlockData.letterAt (D : BlockData N) (k : ℕ) : Fin N :=
  ⟨min k (N - 1), by
    rcases Nat.eq_zero_or_pos N with h | h
    · exact absurd D.uPos.2 (by omega)
    · omega⟩
def BlockData.LevelOK (D : BlockData N) (j : Fin D.T.t → ℕ) (jp : ℕ) : Prop :=
  (∀ i, j i ≤ D.LL.deg (D.letterAt (D.T.pos i)) ∧ j i ≤ D.LL.deg (D.letterAt (D.T.pos i + 1))) ∧
    jp ≤ min (D.LL.deg D.uPos) D.B
def BlockData.gens (O : Type*) [CommRing O] [IsDomain O] [NeZero r] (D : BlockData N) (j : Fin D.T.t → ℕ)
    (jp : ℕ) : Set (MvPolynomial (BVar N r D.T.t) (KK O)) :=
  {x | ∃ y ∈ YjtZ O (r := r) (D.lettersAt j jp) D.T.J D.T.thr, ∃ g ∈ XiPolZ O N r D.T.t (D.B - jp),
    x = (∏ i, D.Ehat O (r := r) i ^ j i) * D.Eplus O (r := r) ^ jp *
      (∏ i, X (scalZ N r D.T.t (Fin.castSucc i)) ^ D.T.z i) * X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus *
      rename (chainEmb N r D.T.t) y * g}
def BlockData.SSZ (O : Type*) [CommRing O] [IsDomain O] [NeZero r] (D : BlockData N) :
    Submodule O (MvPolynomial (BVar N r D.T.t) (KK O)) :=
  Submodule.span O (⋃ (j : Fin D.T.t → ℕ) (jp : ℕ) (_ : D.LevelOK j jp), D.gens O (r := r) j jp)
def BlockData.withMargin (D : BlockData N) (cap : Fin D.T.q → WithTop ℤ) (m : ℝ) : BlockData N :=
  { D with T := { D.T with thr := fun k => (cap k).map (fun x : ℤ => ⌊(x : ℝ) - m⌋) } }
structure SegData (s : ℕ) where
  sigma : ℕ
  G : ℕ
  d : Fin s → ℕ
  bTop : Fin s → ℕ
  bPlus : ℕ
  a : ℕ
  Y : ℝ
  La : ℝ
  E0 : ℝ
structure SegBlock (s r : ℕ) where
  rz : Fin s → Fin (r + 1) → ℕ
  ry : Fin s → Fin (r + 1) → ℕ
  o : Fin s → ℕ
  w : Fin s → ℕ
  sg : Fin s → ℕ
  oPlus : ℕ
variable {s : ℕ}
def SegData.P (p : ℕ) (S : SegData s) (i : Fin s) : ℕ := p ^ (S.G - S.d i)
def SegData.Qj (p : ℕ) (S : SegData s) : ℕ := p ^ S.G
def SegData.t (S : SegData s) : ℕ := s - S.sigma
def SegData.A0 (p : ℕ) (S : SegData s) : ℤ := ⌊((S.a : ℝ) - S.E0) / (S.Qj p : ℝ)⌋
def coarseA (p : ℕ) {r : ℕ} (S : SegData s) (b : SegBlock s r) (i : Fin s) : ℕ :=
  (S.bTop i - ∑ c, b.rz i c) / S.P p i
def coarseC (p : ℕ) {r : ℕ} (S : SegData s) (aTop : Fin s → ℕ) (b : SegBlock s r) (i : Fin s) : ℕ :=
  (aTop i - ∑ c, b.ry i c) / S.P p i
def oEff {r : ℕ} (S : SegData s) (b : SegBlock s r) (i : Fin s) : ℕ :=
  if (i : ℕ) < S.sigma then b.w i + b.sg i else b.o i
def cap (p : ℕ) {r : ℕ} (S : SegData s) (b : SegBlock s r) (l : ℕ) : ℤ :=
  S.A0 p + ∑ i : Fin s, if (i : ℕ) < l then ((coarseA p S b i : ℤ) - (oEff S b i : ℤ)) else 0
def Oplus (p r : ℕ) (S : SegData s) (b : SegBlock s r) : ℝ :=
  (cap p S b s : ℝ) + (S.La / (r + 1) + 4 / (p : ℝ) ^ 2) * ∑ i, 2 * (S.a : ℝ) / (S.P p i : ℝ) +
    S.La * (S.bPlus : ℝ) / (r + 1)
def DigitsOK (p : ℕ) {r : ℕ} (S : SegData s) (aTop : Fin s → ℕ) (b : SegBlock s r) : Prop :=
  (∀ i c, b.rz i c < S.P p i ∧ b.ry i c < S.P p i) ∧
  (∀ i, ∑ c, b.rz i c ≤ S.bTop i ∧ S.P p i ∣ S.bTop i - ∑ c, b.rz i c) ∧
  (∀ i, ∑ c, b.ry i c ≤ aTop i ∧ S.P p i ∣ aTop i - ∑ c, b.ry i c)
def Kept (p r : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (b : SegBlock s r) : Prop :=
  DigitsOK p S aTop b ∧
  (∀ i : Fin s, S.sigma ≤ (i : ℕ) →
    b.o i ≤ coarseA p S b i ∧
    (b.o i : ℝ) ≤ (cap p S b i : ℝ) + S.La * (coarseA p S b i : ℝ) / (r + 1) ∧
    b.w i = 0 ∧ b.sg i = 0) ∧
  (∀ i : Fin s, (i : ℕ) < S.sigma →
    b.o i = 0 ∧ b.w i ≤ coarseA p S b i ∧ b.sg i ≤ coarseC p S aTop b i ∧
    ((b.w i + b.sg i : ℕ) : ℝ) ≤ (coarseA p S b i : ℝ) * (1 + 4 / (p : ℝ) ^ 2) +
      S.La * (cap p S b i : ℝ) / (r + 1) ∧
    (b.sg i : ℝ) ≤ 2 * S.La * (S.A0 p : ℝ) / (r + 1)) ∧
  (b.oPlus : ℝ) ≤ Oplus p r S b
def topOf (a : Fin (2 * s + 1)) (h : (a : ℕ) ≠ 2 * s) : Fin s := ⟨(a : ℕ) / 2, by omega⟩
def segChain (p : ℕ) {r : ℕ} (S : SegData s) (aTop : Fin s → ℕ) (b : SegBlock s r) : ChainLetters (2 * s + 1) where
  vec := fun a => decide ((a : ℕ) % 2 = 0)
  deg := fun a =>
    if h : (a : ℕ) = 2 * s then b.oPlus
    else if (a : ℕ) % 2 = 0 then
      (if ((topOf a h : Fin s) : ℕ) < S.sigma then b.w (topOf a h) else b.o (topOf a h))
    else
      (if ((topOf a h : Fin s) : ℕ) < S.sigma then coarseC p S aTop b (topOf a h) - b.sg (topOf a h)
       else coarseC p S aTop b (topOf a h))
def uTop (S : SegData s) (l : Fin S.t) : Fin s := ⟨S.sigma + l, by have := l.2; unfold SegData.t at this; omega⟩
def segmentCapacities (p : ℕ) {r : ℕ} (S : SegData s) (b : SegBlock s r) : Fin (S.t + 1) → WithTop ℤ :=
  fun q => if h : (q : ℕ) < S.t then ((cap p S b (uTop S ⟨q, h⟩) : ℤ) : WithTop ℤ) else ((cap p S b s : ℤ) : WithTop ℤ)
def segTies (p : ℕ) {r : ℕ} (S : SegData s) (b : SegBlock s r) : TieData where
  t := S.t
  pos := fun l => 2 * (uTop S l : ℕ)
  z := fun l => coarseA p S b (uTop S l) - b.o (uTop S l)
  q := S.t + 1
  J := fun q => if h : (q : ℕ) < S.t then 2 * (uTop S ⟨q, h⟩ : ℕ) + 1 else 2 * s + 1
  thr := segmentCapacities p S b
def blockBase (p : ℕ) {r : ℕ} (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (b : SegBlock s r) :
    BlockData (2 * s + 1) where
  LL := segChain p S aTop b
  T := segTies p S b
  uPos := ⟨2 * s, by omega⟩
  B := S.bPlus
  zPlus := aPlus - b.oPlus
def blockData (p : ℕ) {r : ℕ} (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ) (b : SegBlock s r) :
    BlockData (2 * s + 1) :=
  (blockBase p S aTop aPlus b).withMargin (segmentCapacities p S b) m
def specConst (p : ℕ) {r : ℕ} (S : SegData s) (b : SegBlock s r) : ℕ :=
  ∏ i : Fin s, if (i : ℕ) < S.sigma then (coarseA p S b i - b.w i).factorial * (b.sg i).factorial else 1
def vLE {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) (x : KK O) (D : ℝ) : Prop :=
  ∃ q : ℚ, vK p x = (q : WithTop ℚ) ∧ (q : ℝ) ≤ D
def bbSpec (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) (σ : Type*) (sp : ℕ) :
    Submodule O (MvPolynomial σ (KK O)) :=
  Submodule.span O {F | ∃ (μ : σ →₀ ℕ) (c : KK O),
    (0 : WithTop ℚ) ≤ vK p c + (((padicValNat p (expFact μ) : ℚ) / 2 + (padicValNat p sp : ℚ) / 2 : ℚ) : WithTop ℚ) ∧
    F = monomial μ c}
def blockLat (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p r : ℕ) [NeZero r]
    (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ) (b : SegBlock s r) :
    Submodule O (MvPolynomial (BVar (2 * s + 1) r S.t) (KK O)) :=
  let L : Submodule O (MvPolynomial (BVar (2 * s + 1) r S.t) (KK O)) :=
    (blockData p S aTop aPlus m b).SSZ O (r := r)
  (Submodule.span (KK O) (L : Set (MvPolynomial (BVar (2 * s + 1) r S.t) (KK O)))).restrictScalars O ⊓
    bbSpec O p (BVar (2 * s + 1) r S.t) (specConst p S b)
abbrev SegVs (O : Type*) [CommRing O] [IsDomain O] (r s t : ℕ) :=
  SegBlock s r → MvPolynomial (BVar (2 * s + 1) r t) (KK O)
open Classical in

def segLat (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p r : ℕ) [NeZero r]
    (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ) : Submodule O (SegVs O r s S.t) :=
  Submodule.pi Set.univ (fun b => if Kept p r S aTop b then blockLat O p r S aTop aPlus m b else ⊥)
def segForm (O : Type*) [CommRing O] [IsDomain O] (p r : ℕ) (S : SegData s) :
    SegVs O r s S.t → SegVs O r s S.t → KK O :=
  fun f g => ∑ᶠ b, ((specConst p S b : ℕ) : KK O) * fock (f b) (g b)
def SatIn {O V : Type*} [CommRing O] [AddCommGroup V] [Module O V] (L L₁ : Submodule O V) : Prop :=
  L₁ ≤ L ∧ ∀ (c : O) (x : V), c ≠ 0 → x ∈ L → c • x ∈ L₁ → x ∈ L₁
def PrimIn {O V : Type*} [CommRing O] [AddCommGroup V] [Module O V] (L₁ : Submodule O V) (u : V) : Prop :=
  u ∈ L₁ ∧ ∀ (c : O) (x : V), x ∈ L₁ → u = c • x → IsUnit c
def GoodSub {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) {V : Type*}
    [AddCommGroup V] [Module O V] (be : V → V → KK O) (L L₁ : Submodule O V) (D : ℝ) : Prop :=
  SatIn L L₁ ∧ ∀ u, PrimIn L₁ u → ∃ u' ∈ L, vLE p (be u u') D
def GoodShare {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) {V : Type*}
    [AddCommGroup V] [Module O V] (be : V → V → KK O) (L : Submodule O V) (D κ : ℝ) : Prop :=
  ∃ L₁ : Submodule O V, GoodSub p be L L₁ D ∧
    (1 - κ) * (Module.finrank O L : ℝ) ≤ (Module.finrank O L₁ : ℝ)
def badShare {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) {V : Type*}
    [AddCommGroup V] [Module O V] (be : V → V → KK O) (L : Submodule O V) (D : ℝ) : ℝ :=
  if Module.finrank O L = 0 then 0 else
    ((Module.finrank O L : ℝ) -
        (sSup {n : ℕ | ∃ L₁ : Submodule O V, GoodSub p be L L₁ D ∧ Module.finrank O L₁ = n} : ℕ)) /
      (Module.finrank O L : ℝ)
def kapT (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p r : ℕ) [NeZero r]
    (S : SegData s) (m D : ℝ) (aTop : Fin s → ℕ) (aPlus : ℕ) : ℝ :=
  badShare p (segForm O p r S) (segLat O p r S aTop aPlus m) D
def blockRank (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p r : ℕ) [NeZero r]
    (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ) (b : SegBlock s r) : ℕ :=
  let L : Submodule O (MvPolynomial (BVar (2 * s + 1) r S.t) (KK O)) :=
    (blockData p S aTop aPlus m b).SSZ O (r := r)
  Module.finrank (KK O) (Submodule.span (KK O) (L : Set (MvPolynomial (BVar (2 * s + 1) r S.t) (KK O))))
open Classical in

def segRank (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p r : ℕ) [NeZero r]
    (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ) : ℕ :=
  ∑ᶠ b : SegBlock s r, if Kept p r S aTop b then blockRank O p r S aTop aPlus m b else 0
def blockOrd (p : ℕ) {r : ℕ} (S : SegData s) (b : SegBlock s r) : ℕ :=
  (∑ i, (S.P p i * oEff S b i + (∑ c : Fin (r + 1), if (c : ℕ) = 0 then 0 else b.rz i c) + b.ry i 0)) +
    b.oPlus
def windowA (r : ℕ) (S : SegData s) : Finset ℕ :=
  Icc S.a ⌊(S.a : ℝ) + (S.a : ℝ) / (((r : ℝ) + 1) * S.Y)⌋₊
section Orbit
variable {n' : ℕ}
def cdist (x y : Fin n') : ℕ := (y.val + n' - x.val) % n'
def evenTops (TT : Finset (Fin n')) : List (Fin n') :=
  (TT.filter (fun s => Even s.val)).sort (· ≤ ·)
def numSeg (TT : Finset (Fin n')) : ℕ := (evenTops TT).length
def segStart (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : Fin n' := (evenTops TT).get j
def segNext (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : Fin n' :=
  (evenTops TT).get ⟨((j : ℕ) + 1) % numSeg TT, Nat.mod_lt _ j.pos⟩
def segG (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : ℕ :=
  if cdist (segStart TT j) (segNext TT j) = 0 then n' else cdist (segStart TT j) (segNext TT j)
def segDists (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : List ℕ :=
  ((TT.filter (fun s => ¬ Even s.val ∧ 0 < cdist (segStart TT j) s ∧ cdist (segStart TT j) s < segG TT j)).image
    (cdist (segStart TT j))).sort (· ≤ ·)
def segS (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : ℕ := (segDists TT j).length
def segPos (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (i : Fin (segS TT j)) : Fin n' :=
  posAdd (segStart TT j) ((segDists TT j).get i)
open Classical in

def segData (p : ℕ) (TT : Finset (Fin n')) (bT : Fin n' → ℕ) (a : ℕ) (b' Y La E0 : ℝ) (j : Fin (numSeg TT)) :
    SegData (segS TT j) where
  sigma := ((List.finRange (segS TT j)).filter
    (fun i => (p : ℝ) ^ ((segDists TT j).get i) < (a : ℝ) / b')).length
  G := segG TT j
  d := fun i => (segDists TT j).get i
  bTop := fun i => bT (segPos TT j i)
  bPlus := bT (segNext TT j)
  a := a
  Y := Y
  La := La
  E0 := E0
def segATop (TT : Finset (Fin n')) (aT : Fin n' → ℕ) (j : Fin (numSeg TT)) : Fin (segS TT j) → ℕ :=
  fun i => aT (segPos TT j i)
def segAPlus (TT : Finset (Fin n')) (aT : Fin n' → ℕ) (j : Fin (numSeg TT)) : ℕ := aT (segNext TT j)
end Orbit
section Tensor
variable {W Qq O Kf : Type*} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [Field Kf] [Algebra O Kf]
variable {n' m : ℕ}
def letterWt (m : ℕ) (d : ℕ) (vec : Bool) : Fin (m + 1) → ℤ :=
  if vec then (fun i => if i = 0 then (d : ℤ) else 0) else (fun i => if i = Fin.last m then -(d : ℤ) else 0)
def hhDeg (aT bT : Fin n' → ℕ) (s : Fin n') (vec : Bool) : ℕ :=
  if vec then (if Even s.val then aT s else bT s) else (if Even s.val then bT s else aT s)
def hhWt (m : ℕ) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) (x : TT × Bool) : Fin (m + 1) → ℤ :=
  letterWt m (hhDeg aT bT x.1.val x.2) x.2
def HHten (O : Type*) {Kf : Type*} [CommRing O] [Field Kf] [Algebra O Kf] {n' m : ℕ} (TT : Finset (Fin n'))
    (aT bT : Fin n' → ℕ) (Λ : Fin n' → Submodule O (Fin (m + 1) → Kf)) :
    Submodule O (MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) :=
  Formalism.GradedWeylDivisibility.tensorLat O Kf fun x : TT × Bool => H0 O m (hhWt m TT aT bT x) (Λ x.1.val)
def VHH (Kf : Type*) [Field Kf] {n' m : ℕ} (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) :
    Submodule Kf (MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) :=
  Formalism.GradedWeylDivisibility.tensorLat Kf Kf fun x : TT × Bool => Formalism.GradedWeylDivisibility.dualWeyl Kf (m + 1) (m + 1) (nuOf (hhWt m TT aT bT x))
def dimHH (Kf : Type*) [Field Kf] {n' m : ℕ} (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) : ℕ :=
  Module.finrank Kf (VHH (m := m) Kf TT aT bT)
def toVHH {O Kf : Type*} [CommRing O] [Field Kf] [Algebra O Kf] {n' m : ℕ} (TT : Finset (Fin n'))
    (aT bT : Fin n' → ℕ) (M : Submodule O (MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf)) :
    Submodule O (VHH (m := m) Kf TT aT bT) :=
  M.comap ((VHH (m := m) Kf TT aT bT).subtype.restrictScalars O)
def HHL (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ)
    (L : Submodule W (Fin (m + 1) → Qq)) : Submodule O (VHH (m := m) Kf TT aT bT) :=
  toVHH TT aT bT (HHten O TT aT bT fun s => extO O ι σ s.val L)
def HHLe (p : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ)
    (e : Edge W Qq (m + 1)) : Submodule O (VHH (m := m) Kf TT aT bT) :=
  toVHH TT aT bT (HHten O TT aT bT fun s => LeAt p ι σ w s.val e)
def AHH (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) : ℤ :=
  ∑ s ∈ TT, (hhDeg aT bT s true : ℤ)
def ReHH (p : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ)
    (e : Edge W Qq (m + 1)) : Submodule O (VHH (m := m) Kf TT aT bT) :=
  scale (algebraMap O Kf w ^ (-AHH TT aT bT)) (HHLe p ι σ w TT aT bT e)
def ReHH' (p : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ)
    (e : Edge W Qq (m + 1)) : Submodule O (Module.Dual Kf (VHH (m := m) Kf TT aT bT)) :=
  scale (algebraMap O Kf w ^ (-AHH TT aT bT)) (Formalism.GradedWeylDivisibility.dualLat O Kf (HHLe p ι σ w TT aT bT e))
def beHH (p : ℕ) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) (F : VHH (m := m) Kf TT aT bT)
    (G : Module.Dual Kf (VHH (m := m) Kf TT aT bT)) : Kf :=
  G (((p : Kf) ^ AHH TT aT bT) • F)
def CCe (p : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) (t c : ℕ)
    (e : Edge W Qq (m + 1)) : Submodule O (VHH (m := m) Kf TT aT bT) :=
  scale (algebraMap O Kf w ^ (-(t : ℤ))) (HHL ι σ TT aT bT e.src) ⊓ ReHH p ι σ w TT aT bT e ⊓
    ⨅ (e' : Edge W Qq (m + 1)) (_ : IsEdge p n' 1 e' ∧ e'.src = e.src ∧ e' ≠ e),
      scale (algebraMap O Kf w ^ (c : ℤ)) (ReHH p ι σ w TT aT bT e')
def CCe' (p : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) (t c : ℕ)
    (e : Edge W Qq (m + 1)) : Submodule O (Module.Dual Kf (VHH (m := m) Kf TT aT bT)) :=
  scale (algebraMap O Kf w ^ (-(t : ℤ))) (Formalism.GradedWeylDivisibility.dualLat O Kf (HHL ι σ TT aT bT e.tgt)) ⊓
    ReHH' p ι σ w TT aT bT e ⊓
    ⨅ (e' : Edge W Qq (m + 1)) (_ : IsEdge p n' 1 e' ∧ e'.tgt = e.tgt ∧ e' ≠ e),
      scale (algebraMap O Kf w ^ (c : ℤ)) (ReHH' p ι σ w TT aT bT e')
end Tensor
def vLEO {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) (z : O) (D : ℝ) : Prop :=
  ∃ q : ℚ, vO p z = (q : WithTop ℚ) ∧ (q : ℝ) ≤ D
def FactorsLE {O Kf V V' : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    [AddCommGroup V] [Module O V] [AddCommGroup V'] [Module O V'] (p : ℕ) (be : V → V' → Kf)
    (A : Submodule O V) (A' : Submodule O V') (n : ℕ) (D : ℝ) : Prop :=
  n = 0 ∨ ∃ (x : Fin n → V) (y : Fin n → V'), (∀ i, x i ∈ A) ∧ (∀ i, y i ∈ A') ∧
    ∃ (z : O) (M : Matrix (Fin n) (Fin n) O), z ≠ 0 ∧ vLEO p z D ∧
      ∀ i j, ∑ l, be (x i) (y l) * algebraMap O Kf (M l j) = if i = j then algebraMap O Kf z else 0
def RhoGE {O Kf V V' : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    [AddCommGroup V] [Module O V] [AddCommGroup V'] [Module O V'] (p : ℕ) (be : V → V' → Kf)
    (A : Submodule O V) (A' : Submodule O V') (D X : ℝ) : Prop :=
  ∃ n : ℕ, X ≤ (n : ℝ) ∧ FactorsLE p be A A' n D
def lambdaScale (C0 N1 a : ℝ) : ℝ := C0 * N1 ^ 2 * Real.log a
def errorTermBound (CE1 CE2 p k N1 Q c a b' La : ℝ) : ℝ :=
  CE1 * (a / p ^ 2 + b' / p + La * N1 * a / (p * k) + La * b' / k) + CE2 * k ^ 2 * N1 * Q ^ 2 * c
def m1G4 (Cm k N1 Q c : ℝ) : ℝ := Cm * k * N1 * Q * c
def m0G4 (Cm k N1 Q c : ℝ) : ℝ := m1G4 Cm k N1 Q c + 12 * c
def kap0G4 (N k p a : ℝ) : ℝ := 2 * N * k * Real.logb p a
def kappaMarginBound (Ck N k Q m N1 b' Y E0 a La : ℝ) : ℝ :=
  Ck * N * (Real.exp (-La / 8) + k * Q * (m + N1 * k) / b' + 1 / Y + k * E0 / a)
def gaussianNumber (q k : ℕ) : ℝ := ((q : ℝ) ^ k - 1) / ((q : ℝ) - 1)
def t0G4 {n' : ℕ} (Ct : ℝ) (p k : ℕ) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) (a b' La Q c : ℝ) : ℝ :=
  (∑ j : Fin (numSeg TT), ∑ i : Fin (segS TT j),
      min (bT (segPos TT j i) : ℝ) ((aT (segStart TT j) : ℝ) / (p : ℝ) ^ ((segDists TT j).get i))) +
    Ct * (TT.card : ℝ) * (a / (p : ℝ) ^ 2 + b' / p + La * a / (p * k) + La * b' / k + k * Q + Q * c)
end Formalism.MainNotions.G


