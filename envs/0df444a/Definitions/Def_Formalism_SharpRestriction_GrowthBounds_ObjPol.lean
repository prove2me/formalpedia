-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
-- name    : Formalism_SharpRestriction_GrowthBounds_ObjPol
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:10:16.311129+00:00
-- url     : https://prove2.me/theorems/ca931528-58fc-43fc-906c-ef96280d70db
-- title:
--   Obj Pol
-- statement:
--   Definitions and structural lemmas for Obj Pol, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ObjPol.lean

import Mathlib
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
structure UniformizedDVR (p : ℕ) (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] where

  w : O
  w_irr : Irreducible w

  p_mem : (p : O) ∈ IsLocalRing.maximalIdeal O
  p_ne : (p : O) ≠ 0

  complete : IsAdicComplete (IsLocalRing.maximalIdeal O) O
variable {p : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
def UniformizedDVR.SqP (S : UniformizedDVR p O) : Prop := S.w ^ 2 = (p : O)
abbrev KK (O : Type*) [CommRing O] [IsDomain O] := FractionRing O
abbrev FF (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] := IsLocalRing.ResidueField O
def ramE (p : ℕ) (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : ℕ :=
  (IsDiscreteValuationRing.addVal O (p : O)).toNat
open Classical in

def ordW (x : KK O) : WithTop ℤ :=
  if x = 0 then ⊤ else
    let ab := Classical.choose (IsLocalization.surj (nonZeroDivisors O) x)
    (((IsDiscreteValuationRing.addVal O ab.1).toNat : ℤ) - ((IsDiscreteValuationRing.addVal O (ab.2 : O)).toNat : ℤ) : ℤ)
def vK (p : ℕ) (x : KK O) : WithTop ℚ :=
  (ordW x).map (fun k : ℤ => (k : ℚ) / (ramE p O : ℚ))
def vO (p : ℕ) (x : O) : WithTop ℚ := vK p (algebraMap O (KK O) x)
structure Letters (ι : Type*) where
  vec : ι → Bool
def multideg {ι : Type*} {n : ℕ} (m : ι × Fin n →₀ ℕ) (i : ι) : ℕ := ∑ c : Fin n, m (i, c)
def Pol (R : Type*) [CommSemiring R] {ι : Type*} (n : ℕ) (d : ι → ℕ) :
    Submodule R (MvPolynomial (ι × Fin n) R) :=
  MvPolynomial.restrictSupport R {m | ∀ i, multideg m i = d i}
def IntPol (O : Type*) [CommRing O] [IsDomain O] (σ : Type*) :
    Submodule O (MvPolynomial σ (KK O)) :=
  LinearMap.range (MvPolynomial.mapAlgHom (Algebra.ofId O (KK O)) :
    MvPolynomial σ O →ₐ[O] MvPolynomial σ (KK O)).toLinearMap
def expFact {σ : Type*} (m : σ →₀ ℕ) : ℕ := m.prod fun _ k => k.factorial
def fock {R : Type*} [CommSemiring R] {σ : Type*} (F G : MvPolynomial σ R) : R :=
  ∑ m ∈ F.support, F.coeff m * G.coeff m * (expFact m : R)
def vBB (p : ℕ) {σ : Type*} (F : MvPolynomial σ (KK O)) : WithTop ℚ :=
  F.support.inf fun m => vK p (F.coeff m) + (((padicValNat p (expFact m) : ℚ) / 2 : ℚ) : WithTop ℚ)
def InBB (p : ℕ) {σ : Type*} (F : MvPolynomial σ (KK O)) : Prop := (0 : WithTop ℚ) ≤ vBB (O := O) p F
def lg (p r : ℕ) (a : ℕ) : ℝ := Real.logb p ((a : ℝ) + r) + 1
def kap {ι : Type*} [Fintype ι] (p r : ℕ) (d : ι → ℕ) : ℝ := ∑ i, (r : ℝ) * lg p r (d i)
def genMat (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) R) :=
  Matrix.of fun a b => X (a, b)
abbrev GLCoord (R : Type*) [CommRing R] (n : ℕ) := Localization.Away (genMat R n).det
abbrev GLLaurent (R : Type*) [CommRing R] (n : ℕ) := LaurentPolynomial (GLCoord R n)
def gL (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (GLLaurent R n) :=
  (genMat R n).map fun x => LaurentPolynomial.C (algebraMap _ (GLCoord R n) x)
def gLinv (R : Type*) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (GLLaurent R n) :=
  ((genMat R n).adjugate).map fun x =>
    LaurentPolynomial.C (IsLocalization.Away.invSelf (genMat R n).det * algebraMap _ (GLCoord R n) x)
def twistMat (R : Type*) [CommRing R] (n : ℕ) (j : Fin n) (k : ℤ) : Matrix (Fin n) (Fin n) (GLLaurent R n) :=
  gL R n * Matrix.diagonal (fun a => if a = j then LaurentPolynomial.T k else 1) * gLinv R n
def coefL (R : Type*) [CommRing R] (n : ℕ) : R →+* GLLaurent R n :=
  (LaurentPolynomial.C).comp ((algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)).comp MvPolynomial.C)
open Classical in

def twistSub {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n) :
    MvPolynomial (ι × Fin n) R →+* MvPolynomial (ι × Fin n) (GLLaurent R n) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (coefL R n)) fun v =>
    if v.1 ∈ S then
      (if LL.vec v.1 then ∑ b : Fin n, MvPolynomial.C (twistMat R n j 1 b v.2) * X (v.1, b)
       else ∑ b : Fin n, MvPolynomial.C (twistMat R n j (-1) v.2 b) * X (v.1, b))
    else X v
def sDegs {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    (G : MvPolynomial (ι × Fin n) R) : Finset ℤ :=
  (twistSub LL S j G).support.biUnion fun m => ((twistSub LL S j G).coeff m).coeff.support
def lastIdx (n : ℕ) [NeZero n] : Fin n := ⟨n - 1, Nat.sub_lt (NeZero.pos n) Nat.one_pos⟩
def valS {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (G : MvPolynomial (ι × Fin n) R) : WithTop ℤ :=
  (sDegs LL S (lastIdx n) G).inf fun k => (k : WithTop ℤ)
def lam1S {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (G : MvPolynomial (ι × Fin n) R) : WithBot ℤ :=
  (sDegs LL S (0 : Fin n) G).sup fun k => (k : WithBot ℤ)
def ASet {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι) (th : ℤ) :
    Set (MvPolynomial (ι × Fin n) R) :=
  {F | ((th : ℤ) : WithTop ℤ) ≤ valS LL S F}
def LamSet {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι) (M : ℤ) :
    Set (MvPolynomial (ι × Fin n) R) :=
  {F | lam1S LL S F ≤ ((M : ℤ) : WithBot ℤ)}
open Classical in

def glAct (R : Type*) [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι) (a b : Fin n) :
    MvPolynomial (ι × Fin n) R →ₗ[R] MvPolynomial (ι × Fin n) R :=
  ∑ l : ι,
    if l ∈ S then
      (if LL.vec l then (LinearMap.mulLeft R (X (l, a))) ∘ₗ (pderiv (l, b)).toLinearMap
       else -((LinearMap.mulLeft R (X (l, b))) ∘ₗ (pderiv (l, a)).toLinearMap))
    else 0
def digitOf {σ : Type*} (P : ℕ) (m : σ →₀ ℕ) : σ → ℕ := fun k => m k % P
def coarseOf {σ : Type*} (P : ℕ) (m : σ →₀ ℕ) : σ → ℕ := fun k => m k / P
def DigitClass (R : Type*) [CommSemiring R] {σ : Type*} (P : ℕ) (rho : σ → ℕ) :
    Submodule R (MvPolynomial σ R) :=
  MvPolynomial.restrictSupport R {m | digitOf P m = rho}
def phDig (R : Type*) [CommSemiring R] {σ : Type*} (P : ℕ) : MvPolynomial (σ ⊕ σ) R →ₐ[R] MvPolynomial σ R :=
  MvPolynomial.aeval (Sum.elim X fun k => X k ^ P)
def cUnit (P n : ℕ) : ℚ := ((P * n).factorial : ℚ) / (((P.factorial : ℚ) ^ n) * (n.factorial : ℚ))
def dUnit (P n rho : ℕ) : ℚ := ∏ y ∈ Finset.Icc 1 rho, (1 + (P : ℚ) * n / y)
def digitOfL {σ : Type*} (P : σ → ℕ) (m : σ →₀ ℕ) : σ → ℕ := fun k => m k % P k
def coarseOfL {σ : Type*} (P : σ → ℕ) (m : σ →₀ ℕ) : σ → ℕ := fun k => m k / P k
def DigitClassL (R : Type*) [CommSemiring R] {σ : Type*} (P : σ → ℕ) (rho : σ → ℕ) :
    Submodule R (MvPolynomial σ R) :=
  MvPolynomial.restrictSupport R {m | digitOfL P m = rho}
def phDigL (R : Type*) [CommSemiring R] {σ : Type*} (P : σ → ℕ) : MvPolynomial (σ ⊕ σ) R →ₐ[R] MvPolynomial σ R :=
  MvPolynomial.aeval (Sum.elim X fun k => X k ^ P k)
def divDer {R : Type*} [CommSemiring R] {σ : Type*} (be : σ →₀ ℕ) (F : MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ m ∈ F.support, if be ≤ m then
    MvPolynomial.monomial (m - be) (F.coeff m * ((be.prod fun k j => (m k).choose j : ℕ) : R)) else 0
def wtS {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι) (m : ι × Fin n →₀ ℕ) : Fin n → ℤ :=
  open Classical in
  fun a => ∑ l : ι, if l ∈ S then (if LL.vec l then (m (l, a) : ℤ) else -(m (l, a) : ℤ)) else 0
open Classical in

def divPowMono (R : Type*) [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a b : Fin n) (k : ℕ) (m : ι × Fin n →₀ ℕ) : MvPolynomial (ι × Fin n) R :=
  ∑ f ∈ Finset.finsuppAntidiag (Finset.univ.filter (· ∈ S)) k,
    MvPolynomial.monomial
      ((m - ∑ l ∈ f.support, Finsupp.single (if LL.vec l then (l, b) else (l, a)) (f l))
        + ∑ l ∈ f.support, Finsupp.single (if LL.vec l then (l, a) else (l, b)) (f l))
      (∏ l ∈ f.support, (if LL.vec l then ((m (l, b)).choose (f l) : R)
        else (-1 : R) ^ (f l) * ((m (l, a)).choose (f l) : R)))
def divPow (R : Type*) [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a b : Fin n) (k : ℕ) : MvPolynomial (ι × Fin n) R →ₗ[R] MvPolynomial (ι × Fin n) R :=
  (MvPolynomial.basisMonomials (ι × Fin n) R).constr R (divPowMono R LL S a b k)
def binomPol (R : Type*) [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a : Fin n) (k : ℕ) : MvPolynomial (ι × Fin n) R →ₗ[R] MvPolynomial (ι × Fin n) R :=
  (MvPolynomial.basisMonomials (ι × Fin n) R).constr R
    (fun m => MvPolynomial.monomial m ((Ring.choose (wtS LL S m a) k : ℤ) : R))
def polUZgens (R : Type*) [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι) :
    Set (MvPolynomial (ι × Fin n) R →ₗ[R] MvPolynomial (ι × Fin n) R) :=
  {u | (∃ a b k, a ≠ b ∧ u = divPow R LL S a b k) ∨ (∃ a k, u = binomPol R LL S a k)}
def polGenSub (R : Type*) [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (G : MvPolynomial (ι × Fin n) R) : Submodule R (MvPolynomial (ι × Fin n) R) :=
  Submodule.span R {x | ∃ u ∈ Submonoid.closure (polUZgens R LL S), x = u G}
def polWts {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (W : Submodule R (MvPolynomial (ι × Fin n) R)) : Set (Fin n → ℤ) :=
  {mu | ∃ x ∈ W, x ≠ 0 ∧ ∀ m ∈ x.support, wtS LL S m = mu}
def PolUZStable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra A R] {ι : Type*} [Fintype ι] {n : ℕ}
    (LL : Letters ι) (S : Set ι) (M : Submodule A (MvPolynomial (ι × Fin n) R)) : Prop :=
  ∀ u ∈ polUZgens R LL S, ∀ x ∈ M, u x ∈ M
abbrev GLOps (n : ℕ) (K V : Type*) [Field K] [AddCommGroup V] [Module K V] := Fin n → Fin n → Module.End K V
variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
def weightSp (E : GLOps n K V) (mu : Fin n → ℤ) : Submodule K V :=
  ⨅ a, LinearMap.ker (E a a - (mu a : K) • (1 : Module.End K V))
def IsGLRep (E : GLOps n K V) : Prop :=
  (∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0)) ∧
  (∀ x : V, ∃ W : Submodule K V, FiniteDimensional K W ∧ x ∈ W ∧ ∀ a b, ∀ y ∈ W, E a b y ∈ W) ∧
  (⨆ mu : Fin n → ℤ, weightSp E mu) = ⊤
def wtsOf (E : GLOps n K V) (W : Submodule K V) : Set (Fin n → ℤ) := {mu | weightSp E mu ⊓ W ≠ ⊥}
def Dominant (mu : Fin n → ℤ) : Prop := Antitone mu
def dualWt (lam : Fin n → ℤ) : Fin n → ℤ := fun a => -lam (Fin.rev a)
def rootW (a b : Fin n) : Fin n → ℤ := Pi.single a 1 - Pi.single b 1
def ellOf (E : GLOps n K V) (W : Submodule K V) : ℕ :=
  sSup {k | ∃ mu ∈ wtsOf E W, ∃ nu ∈ wtsOf E W, ∃ a b, a ≠ b ∧ mu - nu = (k : ℤ) • rootW a b}
def ellWt [NeZero n] (lam : Fin n → ℤ) : ℕ := (lam 0 - lam (lastIdx n)).toNat
def deF (p n k : ℕ) : ℕ := Nat.log p (k + n - 1)
def N0 (n : ℕ) : ℕ := n * (n - 1) / 2
def divPowE (E : GLOps n K V) (a b : Fin n) (k : ℕ) : Module.End K V := ((k.factorial : K)⁻¹) • (E a b) ^ k
def binomE (E : GLOps n K V) (a : Fin n) (k : ℕ) : Module.End K V :=
  ((k.factorial : K)⁻¹) • ((List.range k).map fun j : ℕ => E a a - (j : K) • (1 : Module.End K V)).prod
def UZgens (E : GLOps n K V) : Set (Module.End K V) :=
  {u | (∃ a b k, a ≠ b ∧ u = divPowE E a b k) ∨ (∃ a k, u = binomE E a k)}
def UZmon (E : GLOps n K V) : Submonoid (Module.End K V) := Submonoid.closure (UZgens E)
def Umon (E : GLOps n K V) : Submonoid (Module.End K V) := Submonoid.closure (Set.range fun ab : Fin n × Fin n => E ab.1 ab.2)
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
def UZStable [Module O V] [Algebra O K] [IsScalarTower O K V] (E : GLOps n K V) (M : Submodule O V) : Prop := ∀ u ∈ UZgens E, ∀ x ∈ M, u x ∈ M
def UZLattice [Module O V] [Algebra O K] [IsScalarTower O K V] (E : GLOps n K V) (M : Submodule O V) : Prop :=
  UZStable (O := O) E M ∧ M.FG
def MQ [Module O V] [Algebra O K] [IsScalarTower O K V] (M : Submodule O V) : Submodule K V := Submodule.span K (M : Set V)
def IsHWV (E : GLOps n K V) (lam : Fin n → ℤ) (v : V) : Prop :=
  v ≠ 0 ∧ v ∈ weightSp E lam ∧ ∀ a b, a < b → E a b v = 0
def IsIrrHW (E : GLOps n K V) (lam : Fin n → ℤ) (v : V) : Prop :=
  IsGLRep E ∧ Dominant lam ∧ IsHWV E lam v ∧ Submodule.span K {x | ∃ u ∈ Umon E, x = u v} = ⊤
def Delta [Module O V] [Algebra O K] [IsScalarTower O K V] (E : GLOps n K V) (v : V) : Submodule O V :=
  Submodule.span O {x | ∃ u ∈ UZmon E, x = u v}
def otherWts (E : GLOps n K V) (lam : Fin n → ℤ) : Submodule K V := ⨆ mu ∈ {mu | mu ≠ lam}, weightSp E mu
def Nabla [Module O V] [Algebra O K] [IsScalarTower O K V] (E : GLOps n K V) (lam : Fin n → ℤ) (v : V) : Set V :=
  {x | ∀ u ∈ UZmon E, ∃ c : O, u x - (algebraMap O K c) • v ∈ otherWts E lam}
def NablaSub [Module O V] [Algebra O K] [IsScalarTower O K V] (E : GLOps n K V) (lam : Fin n → ℤ) (v : V) :
    Submodule O V where
  carrier := Nabla (O := O) E lam v
  zero_mem' := fun u _ => ⟨0, by simp⟩
  add_mem' := by
    intro x y hx hy u hu
    obtain ⟨c, hc⟩ := hx u hu
    obtain ⟨d, hd⟩ := hy u hu
    refine ⟨c + d, ?_⟩
    have : u (x + y) - (algebraMap O K (c + d)) • v = (u x - (algebraMap O K c) • v) + (u y - (algebraMap O K d) • v) := by
      rw [map_add, map_add, add_smul]; abel
    rw [this]; exact Submodule.add_mem _ hc hd
  smul_mem' := by
    intro a x hx u hu
    obtain ⟨c, hc⟩ := hx u hu
    refine ⟨a * c, ?_⟩
    have : u (a • x) - (algebraMap O K (a * c)) • v = (algebraMap O K a) • (u x - (algebraMap O K c) • v) := by
      rw [← algebraMap_smul K a x, map_smul, map_mul, smul_sub, mul_smul]
    rw [this]; exact Submodule.smul_mem _ _ hc
def isoSub (E : GLOps n K V) (lam : Fin n → ℤ) : Submodule K V :=
  Submodule.span K {x | ∃ u ∈ Umon E, ∃ v, IsHWV E lam v ∧ x = u v}
def IsIsoProj (E : GLOps n K V) (lam : Fin n → ℤ) (e : Module.End K V) : Prop :=
  (∀ x ∈ isoSub E lam, e x = x) ∧ ∀ mu, mu ≠ lam → ∀ x ∈ isoSub E mu, e x = 0
def IsWtProj (E : GLOps n K V) (mu : Fin n → ℤ) (e : Module.End K V) : Prop :=
  (∀ x ∈ weightSp E mu, e x = x) ∧ ∀ nu, nu ≠ mu → ∀ x ∈ weightSp E nu, e x = 0
def IsInvProj (E : GLOps n K V) (e : Module.End K V) : Prop := IsIsoProj E 0 e
def HStrip (nu mu : Fin n → ℤ) (b : ℕ) : Prop :=
  (∀ a, nu a ≤ mu a) ∧ (∀ a : Fin n, ∀ h : a.1 + 1 < n, mu ⟨a.1 + 1, h⟩ ≤ nu a) ∧ ∑ a, (mu a - nu a) = (b : ℤ)
structure PPath (n N : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) where
  mu : Fin (N + 1) → Fin n → ℤ
  zero : mu 0 = 0
  dom : ∀ i, Dominant (mu i)
  step : ∀ i : Fin N, if LL.vec i then HStrip (mu i.castSucc) (mu i.succ) (B i) else HStrip (mu i.succ) (mu i.castSucc) (B i)
def PPath.h {N : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} (P : PPath n N LL B) (i : Fin (N + 1)) (c : ℤ) : ℕ :=
  (Finset.univ.filter fun m => c ≤ P.mu i m).card
abbrev WF (p f : ℕ) [Fact p.Prime] := WittVector p (GaloisField p f)
def sigPow (p f : ℕ) [Fact p.Prime] (s : ℤ) : WF p f →+* WF p f :=
  (WittVector.frobenius : WF p f →+* WF p f) ^ (s % (f : ℤ)).toNat
structure LiftLetters (ι : Type*) extends Letters ι where
  pos : ι → ℤ
variable {p f : ℕ} [Fact p.Prime]
def sigMat (p f : ℕ) [Fact p.Prime] (O : Type*) [CommRing O] [IsDomain O] [Algebra (WF p f) O] {k : ℕ}
    (g : Matrix (Fin k) (Fin k) (WF p f)) (s : ℤ) : Matrix (Fin k) (Fin k) (KK O) :=
  Matrix.of fun a b => algebraMap O (KK O) (algebraMap (WF p f) O (sigPow p f s (g a b)))
def IsGLW {k : ℕ} (g : Matrix (Fin k) (Fin k) (WF p f)) : Prop := IsUnit g.det
open Classical in

def liftSubst (p f : ℕ) [Fact p.Prime] (O : Type*) [CommRing O] [IsDomain O] [Algebra (WF p f) O]
    (w : O) (r : ℕ) {ι : Type*} {k : ℕ} (LL : LiftLetters ι) (g : Matrix (Fin k) (Fin k) (WF p f)) :
    MvPolynomial (ι × Fin k) (KK O) →ₐ[KK O] MvPolynomial (ι × Fin k) (KK O) :=
  MvPolynomial.aeval fun v =>
    if LL.vec v.1 then
      ∑ b : Fin k, (if r ≤ b.val then C (algebraMap O (KK O) w) * X (v.1, b) else X (v.1, b)) *
        C ((sigMat p f O g (LL.pos v.1))⁻¹ b v.2)
    else
      ∑ b : Fin k, (if b.val < r then C (algebraMap O (KK O) w) * X (v.1, b) else X (v.1, b)) *
        C (sigMat p f O g (LL.pos v.1) v.2 b)
def InWj {O : Type*} [CommRing O] [IsDomain O] {σ : Type*} (w : O) (P : MvPolynomial σ (KK O)) (j : ℕ) : Prop :=
  ∀ m, ∃ c : O, P.coeff m = algebraMap O (KK O) (w ^ j * c)
def InA {O : Type*} [CommRing O] [IsDomain O] {σ : Type*} (P : MvPolynomial σ (KK O)) : Prop :=
  ∀ m, ∃ c : O, P.coeff m = algebraMap O (KK O) c
def InWjRg (p f : ℕ) [Fact p.Prime] (O : Type*) [CommRing O] [IsDomain O] [Algebra (WF p f) O]
    (w : O) (r : ℕ) {ι : Type*} {k : ℕ} (LL : LiftLetters ι) (g : Matrix (Fin k) (Fin k) (WF p f))
    (F : MvPolynomial (ι × Fin k) (KK O)) (j : ℕ) : Prop :=
  InWj w (liftSubst p f O w r LL g F) j
def ordG (p f : ℕ) [Fact p.Prime] (O : Type*) [CommRing O] [IsDomain O] [Algebra (WF p f) O]
    (w : O) (r : ℕ) {ι : Type*} {k : ℕ} (LL : LiftLetters ι) (g : Matrix (Fin k) (Fin k) (WF p f))
    (F : MvPolynomial (ι × Fin k) (KK O)) : ℕ∞ :=
  ⨆ j ∈ {j : ℕ | InWjRg p f O w r LL g F j}, (j : ℕ∞)
def ratPlane (p f : ℕ) [Fact p.Prime] (r : ℕ) {k : ℕ} (g : Matrix (Fin k) (Fin k) (WF p f)) :
    Submodule (GaloisField p f) (Fin k → GaloisField p f) :=
  Submodule.span (GaloisField p f) {x | ∃ i : Fin k, i.val < r ∧ x = fun c => WittVector.constantCoeff (g⁻¹ i c)}
structure AdmissibleDVR (p n' : ℕ) (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  two_le : 2 ≤ n'
  even : Even n'
  over_Fq : ∃ k : Subfield (FF O), Nat.card k = p ^ n'
section Extremal
variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
def nMinus (E : GLOps n K V) : Submodule K V :=
  ⨆ a : Fin n, ⨆ b : Fin n, ⨆ (_ : b < a), LinearMap.range (E a b)
def ppFac (E : GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n) (T : ℕ) : Module.End K V :=
  ∑ k ∈ Finset.range (T + 1),
    ((-1 : K) ^ k / ((Nat.choose ((mu a - mu b + ((b : ℤ) - (a : ℤ))).toNat + k) k : ℕ) : K)) •
      (divPowE E b a k * divPowE E a b k)
def pp (E : GLOps n K V) (mu : Fin n → ℤ) (ord : List (Fin n × Fin n)) (T : ℕ) : Module.End K V :=
  (ord.map fun ab => ppFac E mu ab.1 ab.2 T).prod
end Extremal
def NormalOrder (n : ℕ) (ord : List (Fin n × Fin n)) : Prop :=
  ord.Nodup ∧ (∀ ab ∈ ord, ab.1 < ab.2) ∧ (∀ a b : Fin n, a < b → (a, b) ∈ ord) ∧
    ∀ a b c : Fin n, a < b → b < c →
      (ord.idxOf (a, b) < ord.idxOf (a, c) ∧ ord.idxOf (a, c) < ord.idxOf (b, c)) ∨
      (ord.idxOf (b, c) < ord.idxOf (a, c) ∧ ord.idxOf (a, c) < ord.idxOf (a, b))
open Classical in

def degIn {ι : Type*} [Fintype ι] (d : ι → ℕ) (S : Set ι) : ℕ := ∑ l, if l ∈ S then d l else 0
def glOps (K : Type*) [Field K] {ι : Type*} [Fintype ι] (n : ℕ) (LL : Letters ι) (S : Set ι) :
    GLOps n K (MvPolynomial (ι × Fin n) K) :=
  fun a b => glAct K LL S a b
section SetProj
variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
def IsIsoProjSet (E : GLOps n K V) (T : Set (Fin n → ℤ)) (e : Module.End K V) : Prop :=
  (∀ lam ∈ T, ∀ x ∈ isoSub E lam, e x = x) ∧ ∀ mu, mu ∉ T → ∀ x ∈ isoSub E mu, e x = 0
def jointIsoSub {N : ℕ} (E : Fin N → GLOps n K V) (lam : Fin N → Fin n → ℤ) : Submodule K V :=
  ⨅ i, isoSub (E i) (lam i)
def IsJointProj {N : ℕ} (E : Fin N → GLOps n K V) (T : Set (Fin N → Fin n → ℤ)) (e : Module.End K V) : Prop :=
  (∀ lam ∈ T, ∀ x ∈ jointIsoSub E lam, e x = x) ∧ ∀ mu, mu ∉ T → ∀ x ∈ jointIsoSub E mu, e x = 0
end SetProj
def sumLetters {ι : Type*} (LL : Letters ι) : Letters (ι ⊕ ι) := ⟨Sum.elim LL.vec LL.vec⟩
def sumRename (R : Type*) [CommSemiring R] {ι : Type*} (n : ℕ) :
    MvPolynomial ((ι × Fin n) ⊕ (ι × Fin n)) R →ₐ[R] MvPolynomial ((ι ⊕ ι) × Fin n) R :=
  MvPolynomial.rename (Equiv.sumProdDistrib ι ι (Fin n)).symm
def pEnd {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) : Fin n → ℤ := mu (Fin.last N)
def colH {n : ℕ} (mu : Fin n → ℤ) (c : ℤ) : ℕ := (univ.filter fun m => c ≤ mu m).card
def extOne {n : ℕ} {P : Type*} [CommRing P] : Finset (Fin n) → P := fun J => if J = ∅ then 1 else 0
def wedgeR {n : ℕ} {P : Type*} [CommRing P] (x : Fin n → P) (K : Finset (Fin n) → P) : Finset (Fin n) → P :=
  fun J => ∑ m ∈ J, (-1 : P) ^ (J.filter fun j => m < j).card * x m * K (J.erase m)
def contrR {n : ℕ} {P : Type*} [CommRing P] (x : Fin n → P) (K : Finset (Fin n) → P) : Finset (Fin n) → P :=
  fun J => ∑ m ∈ univ \ J, (-1 : P) ^ (J.filter fun j => m < j).card * x m * K (insert m J)
def colStep {n : ℕ} {P : Type*} [CommRing P] (c : ℤ) (hP hN : ℕ) (x : Fin n → P) (K : Finset (Fin n) → P) :
    Finset (Fin n) → P :=
  if hP < hN then (if 1 ≤ c then wedgeR x K else contrR x K)
  else if hN < hP then (if 1 ≤ c then contrR x K else wedgeR x K)
  else K
def letVec (R : Type*) [CommRing R] {N n : ℕ} (i : Fin N) : Fin n → MvPolynomial (Fin N × Fin n) R :=
  fun m => X (i, m)
def Kcol (R : Type*) [CommRing R] {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (c : ℤ) :
    ℕ → Finset (Fin n) → MvPolynomial (Fin N × Fin n) R
  | 0 => extOne
  | j + 1 =>
    if h : j < N then
      colStep c (colH (mu ⟨j, by omega⟩) c) (colH (mu ⟨j + 1, by omega⟩) c) (letVec R ⟨j, h⟩) (Kcol R mu c j)
    else Kcol R mu c j
def colRange {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) : Finset ℤ :=
  let T : ℤ := ∑ i, ∑ m, |mu i m|
  Finset.Icc (-T) T
def Psi (R : Type*) [CommRing R] {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (I : ℤ → Finset (Fin n)) :
    MvPolynomial (Fin N × Fin n) R :=
  ∏ c ∈ colRange mu, Kcol R mu c N (I c)
def Ican {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) : ℤ → Finset (Fin n) := fun c =>
  if 1 ≤ c then univ.filter (fun m : Fin n => m.val < colH (pEnd mu) c)
  else univ.filter (fun m : Fin n => colH (pEnd mu) c ≤ m.val)
def tabCol {n : ℕ} (I : ℤ → Finset (Fin n)) (c : ℤ) : Finset (Fin n) := if 1 ≤ c then I c else univ \ I c
def IsSt {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (I : ℤ → Finset (Fin n)) : Prop :=
  (∀ c, c ∉ colRange mu → I c = ∅) ∧
  (∀ c, (I c).card = if 1 ≤ c then colH (pEnd mu) c else n - colH (pEnd mu) c) ∧
  ∀ c (t : Fin n), ((tabCol I (c + 1)).filter (· ≤ t)).card ≤ ((tabCol I c).filter (· ≤ t)).card
def IsHWVPol (R : Type*) [CommRing R] {N n : ℕ} (LL : Letters (Fin N)) (mu : Fin n → ℤ)
    (G : MvPolynomial (Fin N × Fin n) R) : Prop :=
  G ≠ 0 ∧ (∀ m ∈ G.support, wtS LL Set.univ m = mu) ∧
    ∀ a b : Fin n, a < b → ∀ k : ℕ, 1 ≤ k → divPow R LL Set.univ a b k G = 0
section Symbols
variable {N r K : ℕ}
def plPart (mu : Fin (N + 1) → Fin (r + K) → ℤ) : Fin (N + 1) → Fin r → ℤ := fun i a => mu i (Fin.castAdd K a)
def tanPart (mu : Fin (N + 1) → Fin (r + K) → ℤ) : Fin (N + 1) → Fin K → ℤ := fun i b => mu i (Fin.natAdd r b)
def joinPT (nu : Fin (N + 1) → Fin r → ℤ) (ka : Fin (N + 1) → Fin K → ℤ) : Fin (N + 1) → Fin (r + K) → ℤ :=
  fun i => Fin.append (nu i) (ka i)
def plVar : Fin N × Fin r → Fin N × Fin (r + K) := fun v => (v.1, Fin.castAdd K v.2)
def tanVar : Fin N × Fin K → Fin N × Fin (r + K) := fun v => (v.1, Fin.natAdd r v.2)
def PsiPl (R : Type*) [CommRing R] (nu : Fin (N + 1) → Fin r → ℤ) (I : ℤ → Finset (Fin r)) :
    MvPolynomial (Fin N × Fin (r + K)) R :=
  rename (plVar (K := K)) (Psi R nu I)
def PsiTan (R : Type*) [CommRing R] (ka : Fin (N + 1) → Fin K → ℤ) (I : ℤ → Finset (Fin K)) :
    MvPolynomial (Fin N × Fin (r + K)) R :=
  rename (tanVar (r := r)) (Psi R ka I)
def plTanCol (R : Type*) [CommRing R] (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (J : Finset (Fin (r + K))) :
    MvPolynomial (Fin N × Fin (r + K)) R :=
  rename (plVar (K := K)) (Kcol R (plPart mu) c N (univ.filter fun a => Fin.castAdd K a ∈ J)) *
    rename (tanVar (r := r)) (Kcol R (tanPart mu) c N (univ.filter fun b => Fin.natAdd r b ∈ J))
def joinI (I' : ℤ → Finset (Fin r)) (I'' : ℤ → Finset (Fin K)) : ℤ → Finset (Fin (r + K)) :=
  fun c => (I' c).image (Fin.castAdd K) ∪ (I'' c).image (Fin.natAdd r)
def symWt (LL : Letters (Fin N)) (om : Fin N → ℕ) (v : Fin N × Fin (r + K)) : ℕ :=
  if (LL.vec v.1 = true ∧ r ≤ v.2.val) ∨ (LL.vec v.1 = false ∧ v.2.val < r) then om v.1 else 0
def monWt (LL : Letters (Fin N)) (om : Fin N → ℕ) (m : Fin N × Fin (r + K) →₀ ℕ) : ℕ :=
  Finsupp.weight (symWt (r := r) (K := K) LL om) m
def IsCostly (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (i : Fin N) : Prop :=
  (colH (mu i.castSucc) c < colH (mu i.succ) c ∧ r ≤ colH (mu i.castSucc) c) ∨
  (colH (mu i.succ) c < colH (mu i.castSucc) c ∧ colH (mu i.castSucc) c ≤ r)
open Classical in

def oc (om : Fin N → ℕ) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) : ℕ :=
  ∑ i : Fin N, if IsCostly mu c i then om i else 0
def IsUsed {n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (c : ℤ) (i : Fin N) : Prop :=
  colH (mu i.castSucc) c ≠ colH (mu i.succ) c
end Symbols
section Lifts
variable (p f : ℕ) [Fact p.Prime] {O : Type*} [CommRing O] [IsDomain O] [Algebra (WF p f) O] {k : ℕ}
open Classical in

def degUS {ι : Type*} (LL : LiftLetters ι) (r : ℕ) (m : ι × Fin k →₀ ℕ) : ℕ :=
  ∑ v ∈ m.support, if (LL.vec v.1 = true ∧ r ≤ v.2.val) ∨ (LL.vec v.1 = false ∧ v.2.val < r) then m v else 0
def letG {N : ℕ} (LL : LiftLetters (Fin N)) (g : Matrix (Fin k) (Fin k) (WF p f)) (i : Fin N) :
    Fin k → MvPolynomial (Fin N × Fin k) (KK O) :=
  fun b => if LL.vec i then ∑ a : Fin k, X (i, a) * C (sigMat p f O g (LL.pos i) a b)
    else ∑ a : Fin k, X (i, a) * C ((sigMat p f O g (LL.pos i))⁻¹ b a)
def powC {P' : Type*} [CommRing P'] {k : ℕ} (P : ℕ) (Kv : Finset (Fin k) → P') : Finset (Fin k) → P' :=
  fun J => Kv J ^ P
def KKstate {N : ℕ} (LL : LiftLetters (Fin N)) (g : Matrix (Fin k) (Fin k) (WF p f))
    (mu : Fin (N + 1) → Fin k → ℤ) (c : ℤ) : ℕ → (Finset (Fin k) → MvPolynomial (Fin N × Fin k) (KK O)) × Option ℤ
  | 0 => (extOne, none)
  | j + 1 =>
    if h : j < N then
      let st := KKstate LL g mu c j
      let hP := colH (mu ⟨j, by omega⟩) c
      let hN := colH (mu ⟨j + 1, by omega⟩) c
      if hP = hN then st else
        let P := match st.2 with
          | none => 1
          | some sl => p ^ (LL.pos ⟨j, h⟩ - sl).toNat
        (colStep c hP hN (letG p f (O := O) LL g ⟨j, h⟩) (powC P st.1), some (LL.pos ⟨j, h⟩))
    else KKstate LL g mu c j
def KKc {N : ℕ} (LL : LiftLetters (Fin N)) (g : Matrix (Fin k) (Fin k) (WF p f)) (z : ℤ)
    (mu : Fin (N + 1) → Fin k → ℤ) (c : ℤ) : Finset (Fin k) → MvPolynomial (Fin N × Fin k) (KK O) :=
  let st := KKstate p f (O := O) LL g mu c N
  match st.2 with
  | none => st.1
  | some sl => powC (p ^ (z - sl).toNat) st.1
def powSubst {N : ℕ} (LL : LiftLetters (Fin N)) (z : ℤ) :
    MvPolynomial (Fin N × Fin k) O →ₐ[O] MvPolynomial (Fin N × Fin k) (KK O) :=
  aeval fun v => (X v : MvPolynomial (Fin N × Fin k) (KK O)) ^ (p ^ (z - LL.pos v.1).toNat)
end Lifts
end Formalism.MainNotions.G


