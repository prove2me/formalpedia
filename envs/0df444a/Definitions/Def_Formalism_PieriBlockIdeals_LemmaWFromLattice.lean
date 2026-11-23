-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
-- name    : Formalism_PieriBlockIdeals_LemmaWFromLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:09:30.550419+00:00
-- url     : https://prove2.me/theorems/01de9e92-4a37-4973-8741-9a2fa313cb11
-- title:
--   Lemma WFrom Lattice
-- statement:
--   Definitions and structural lemmas for Lemma WFrom Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/LemmaWFromLattice.lean

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWAssembled
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
section Subst
variable {R : Type} [CommRing R]
def gamSer (lam : R) (un : R⟦X⟧) : R⟦X⟧ := X * (1 + un * (X - C lam))
def gam0 (lam : R) (un y : R⟦X⟧) : R⟦X⟧ := y.subst (gamSer lam un)
def frob0 (l : ℕ) (y : R⟦X⟧) : R⟦X⟧ := y.subst (X ^ l : R⟦X⟧)
end Subst
def IsUn (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (u : ℤ_[l]) (un : O⟦X⟧) :
    Prop :=
  act l O u (pi0 l O) = pi0 l O * (1 + inc l O un * q0 l O)
def IncLaws : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O],
    (∀ f g : O⟦X⟧, inc l O (f + g) = inc l O f + inc l O g) ∧
    (∀ f g : O⟦X⟧, inc l O (f * g) = inc l O f * inc l O g) ∧
    (∀ a : O, inc l O (C a) = C a) ∧ inc l O X = pi0 l O ∧ inc l O (X - C (l : O)) = q0 l O ∧
    (∀ f : O⟦X⟧, constantCoeff (inc l O f) = constantCoeff f) ∧
    (∀ f p : O⟦X⟧, constantCoeff p = 0 → inc l O (f.subst p) = f.subst (inc l O p)) ∧
    (l ≠ 2 → Function.Injective (inc l O))
def IncRed : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O k : Type) [CommRing O] [CommRing k] [Algebra ℤ_[l] O] [Algebra ℤ_[l] k]
    (red : O →+* k), (∀ z : ℤ_[l], red (algebraMap ℤ_[l] O z) = algebraMap ℤ_[l] k z) →
    PowerSeries.map red (pi0 l O) = pi0 l k ∧
    (∀ g : O⟦X⟧, PowerSeries.map red (inc l O g) = inc l k (PowerSeries.map red g)) ∧
    (∀ (c : ℤ_[l]) (f : O⟦X⟧),
      PowerSeries.map red (act l O c f) = act l k c (PowerSeries.map red f)) ∧
    (∀ f : O⟦X⟧, PowerSeries.map red (phi l O f) = phi l k (PowerSeries.map red f))
def GamLaws : Prop :=
  ∀ (R : Type) [CommRing R] (lam : R) (un : R⟦X⟧),
    (∀ f g : R⟦X⟧, gam0 lam un (f + g) = gam0 lam un f + gam0 lam un g) ∧
    (∀ f g : R⟦X⟧, gam0 lam un (f * g) = gam0 lam un f * gam0 lam un g) ∧
    (∀ a : R, gam0 lam un (C a) = C a) ∧
    (∀ y : R⟦X⟧, X ∣ gam0 lam un y - y) ∧
    gam0 lam un X = X * (1 + un * (X - C lam)) ∧
    gam0 lam un (X - C lam) = (1 + X * un) * (X - C lam) ∧
    (∀ y : R⟦X⟧, constantCoeff (gam0 lam un y) = constantCoeff y)
def FrobLaws : Prop :=
  ∀ (R : Type) [CommRing R] (l : ℕ), 0 < l →
    (∀ f g : R⟦X⟧, frob0 l (f + g) = frob0 l f + frob0 l g) ∧
    (∀ f g : R⟦X⟧, frob0 l (f * g) = frob0 l f * frob0 l g) ∧
    (∀ a : R, frob0 l (C a) = C a) ∧ frob0 l (X : R⟦X⟧) = X ^ l
def GamRed : Prop :=
  ∀ (R k : Type) [CommRing R] [CommRing k] (red : R →+* k) (lam : R) (un y : R⟦X⟧),
    PowerSeries.map red (gam0 lam un y) =
      gam0 (red lam) (PowerSeries.map red un) (PowerSeries.map red y)
def GammaOnInc : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (u : ℤ_[l]) (un : O⟦X⟧),
    IsUn l O u un → ∀ y : O⟦X⟧, act l O u (inc l O y) = inc l O (gam0 (l : O) un y)
def UnConst : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra ℤ_[l] O], l ≠ 2 →
    ∀ u c : ℤ_[l], u = 1 + (l : ℤ_[l]) * c → (∃ un : O⟦X⟧, IsUn l O u un) ∧
      ∀ un : O⟦X⟧, IsUn l O u un →
        (∀ un' : O⟦X⟧, IsUn l O u un' → un' = un) ∧
        ∃ e : O, constantCoeff un = algebraMap ℤ_[l] O c + (l : O) * e
def PhiOnInc : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O k : Type) [CommRing O] [CommRing k] [Algebra ℤ_[l] O] [Algebra ℤ_[l] k]
    [CharP k l] (red : O →+* k), l ≠ 2 →
    (∀ z : ℤ_[l], red (algebraMap ℤ_[l] O z) = algebraMap ℤ_[l] k z) → ∀ y : O⟦X⟧,
    (∃ y' : O⟦X⟧, phi l O (inc l O y) = inc l O y') ∧
    ∀ y' : O⟦X⟧, phi l O (inc l O y) = inc l O y' →
      PowerSeries.map red y' = frob0 l (PowerSeries.map red y)
def EvalCong : Prop :=
  ∀ (O : Type) [CommRing O] (lam a : O) (g : O⟦X⟧), (X - C lam) ∣ g - C a →
    (∃ e : O, constantCoeff g = a + lam * e) ∧
    ∀ (k : Type) [CommRing k] (red : O →+* k), red lam = 0 → red (constantCoeff g) = red a
def LinDivisionEval : Prop :=
  ∀ (O : Type) [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [IsTopologicalRing O]
    [IsLinearTopology O O] [T2Space O] [CompleteSpace O] (c a : O) (f f₁ : O⟦X⟧),
    IsTopologicallyNilpotent c → f = (X - C c) * f₁ + C a →
    PowerSeries.eval₂ (RingHom.id O) c f = a
def GammaModQ : Prop :=
  ∀ (O : Type) [CommRing O] (lam : O) (n : ℕ) (D : Matrix (Fin n) (Fin n) O⟦X⟧)
    (Th : Matrix (Fin n) (Fin n) O), (∀ a b, (X - C lam) ∣ D a b - C (Th a b)) →
    ∀ a b, (X - C lam) ∣ (1 + (X : O⟦X⟧) • D) a b - C ((1 + lam • Th) a b)
def DLinear : Prop :=
  ∀ (A N : Type) [CommRing A] [AddCommGroup N] [Module A N] (p : A) (γA : A →+* A) (γ d : N → N),
    (∀ x : N, p • x = 0 → x = 0) → (∀ x y, γ (x + y) = γ x + γ y) →
    (∀ y x, γ (y • x) = γA y • γ x) → (∀ x, p • d x = γ x - x) →
    (∀ x y, d (x + y) = d x + d y) ∧ (∀ a x, γA a = a → d (a • x) = a • d x)
def DbarCoord : Prop :=
  ∀ (k : Type) [CommRing k] (n : ℕ) (un : k⟦X⟧) (D : Matrix (Fin n) (Fin n) k⟦X⟧)
    (y z : Fin n → k⟦X⟧),
    (∀ a, X * z a = ((1 + (X : k⟦X⟧) • D).mulVec fun b => gam0 0 un (y b)) a - y a) →
    ∀ a, constantCoeff (z a) = ((D.map constantCoeff).mulVec fun b => constantCoeff (y b)) a
def DetDvd : Prop :=
  ∀ (R : Type) [CommRing R] (n h : ℕ) (x : R) (P Q : Matrix (Fin n) (Fin n) R),
    P * Q = (x ^ h) • (1 : Matrix (Fin n) (Fin n) R) → P.det ∣ x ^ (h * n)
def BlockHeight : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (π : R) (n h : ℕ) (Φ Φ' : Matrix (Fin n) (Fin n) R)
    (b : Fin n → ℕ), π ≠ 0 → Φ.BlockTriangular b →
    Φ * Φ' = (π ^ h) • (1 : Matrix (Fin n) (Fin n) R) →
    Φ'.BlockTriangular b ∧ ∀ r, Φ.toSquareBlock b r * Φ'.toSquareBlock b r =
      (π ^ h) • (1 : Matrix {j // b j = r} {j // b j = r} R)
def BlockHeightLine : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (π : R) (n h : ℕ) (Φ Φ' : Matrix (Fin n) (Fin n) R)
    (b : Fin n → ℕ) (s : Fin n), π ≠ 0 → Φ.BlockTriangular b →
    Φ * Φ' = (π ^ h) • (1 : Matrix (Fin n) (Fin n) R) → (∀ j, b j = b s → j = s) →
    Φ s s * Φ' s s = π ^ h
def UnitPow : Prop :=
  ∀ (k : Type) [Field k] (h : ℕ) (x x' : k⟦X⟧), x * x' = X ^ h →
    ∃ (α : ℕ) (u : (k⟦X⟧)ˣ), α ≤ h ∧ x = (u : k⟦X⟧) * X ^ α
def PhiDiag : Prop :=
  ∀ (k : Type) [Field k] (l s : ℕ) (p : k⟦X⟧) (v w w' : (k⟦X⟧)ˣ) (κ κ' : ℤ), 0 < l →
    ((frob0 l (w' : k⟦X⟧) : k⟦X⟧) : LaurentSeries k) * ((X : k⟦X⟧) : LaurentSeries k) ^ ((l : ℤ) * κ') *
        (((v : k⟦X⟧) * X ^ s : k⟦X⟧) : LaurentSeries k) =
      (p : LaurentSeries k) * ((w : k⟦X⟧) : LaurentSeries k) * ((X : k⟦X⟧) : LaurentSeries k) ^ κ →
    0 ≤ (l : ℤ) * κ' + (s : ℤ) - κ ∧
      ∃ u : (k⟦X⟧)ˣ, p = (u : k⟦X⟧) * X ^ ((l : ℤ) * κ' + (s : ℤ) - κ).toNat
def ThetaDiag : Prop :=
  ∀ (k : Type) [Field k] (un g c : k⟦X⟧) (w : (k⟦X⟧)ˣ) (κ : ℤ),
    ((gam0 0 un (w : k⟦X⟧) : k⟦X⟧) : LaurentSeries k) * ((gamSer 0 un : k⟦X⟧) : LaurentSeries k) ^ κ *
        ((1 + X * g : k⟦X⟧) : LaurentSeries k) =
      (c : LaurentSeries k) * ((w : k⟦X⟧) : LaurentSeries k) * ((X : k⟦X⟧) : LaurentSeries k) ^ κ →
    constantCoeff c = 1 ∧ coeff 1 c = (κ : k) * constantCoeff un + constantCoeff g
def SemilinChange : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (θ : R →+* R) (M : Matrix (Fin n) (Fin n) R)
    (g g' : (Matrix (Fin n) (Fin n) R)ˣ) (y : Fin n → R),
    M.mulVec (fun a => θ ((g' : Matrix (Fin n) (Fin n) R).mulVec y a)) =
      (g : Matrix (Fin n) (Fin n) R).mulVec
        ((((g⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R) * M *
          (g' : Matrix (Fin n) (Fin n) R).map θ).mulVec fun a => θ (y a))
section Change
variable {k : Type} [CommRing k] {n : ℕ}
def chgPhi (l : ℕ) (g g' : (Matrix (Fin n) (Fin n) k⟦X⟧)ˣ) (P : Matrix (Fin n) (Fin n) k⟦X⟧) :
    Matrix (Fin n) (Fin n) k⟦X⟧ :=
  ((g⁻¹ : (Matrix (Fin n) (Fin n) k⟦X⟧)ˣ) : Matrix (Fin n) (Fin n) k⟦X⟧) * P *
    (g' : Matrix (Fin n) (Fin n) k⟦X⟧).map (frob0 l)
def chgGam (un : k⟦X⟧) (g : (Matrix (Fin n) (Fin n) k⟦X⟧)ˣ) (D : Matrix (Fin n) (Fin n) k⟦X⟧) :
    Matrix (Fin n) (Fin n) k⟦X⟧ :=
  ((g⁻¹ : (Matrix (Fin n) (Fin n) k⟦X⟧)ˣ) : Matrix (Fin n) (Fin n) k⟦X⟧) * (1 + (X : k⟦X⟧) • D) *
    (g : Matrix (Fin n) (Fin n) k⟦X⟧).map (gam0 0 un)
def thetaOf (Γ : Matrix (Fin n) (Fin n) k⟦X⟧) : Matrix (Fin n) (Fin n) k := Γ.map (coeff 1)
end Change
def ThetaBaseChange : Prop :=
  ∀ (k : Type) [CommRing k] (n : ℕ) (un : k⟦X⟧) (g : (Matrix (Fin n) (Fin n) k⟦X⟧)ˣ)
    (D : Matrix (Fin n) (Fin n) k⟦X⟧),
    (chgGam un g D).map constantCoeff = 1 ∧
    thetaOf (chgGam un g D) =
      ((g⁻¹ : (Matrix (Fin n) (Fin n) k⟦X⟧)ˣ) : Matrix (Fin n) (Fin n) k⟦X⟧).map constantCoeff *
        D.map constantCoeff * (g : Matrix (Fin n) (Fin n) k⟦X⟧).map constantCoeff ∧
    (thetaOf (chgGam un g D)).charpoly = (D.map constantCoeff).charpoly
def PhiBaseChange : Prop :=
  ∀ (k : Type) [CommRing k] (n l h : ℕ) (g g' : (Matrix (Fin n) (Fin n) k⟦X⟧)ˣ)
    (P : Matrix (Fin n) (Fin n) k⟦X⟧), 0 < l →
    ((∃ M, P * M = ((X : k⟦X⟧) ^ h) • (1 : Matrix (Fin n) (Fin n) k⟦X⟧)) →
      ∃ M, chgPhi l g g' P * M = ((X : k⟦X⟧) ^ h) • (1 : Matrix (Fin n) (Fin n) k⟦X⟧)) ∧
    ∀ (x : k⟦X⟧) (t : ℕ), MinorsDvd x t P → MinorsDvd x t (chgPhi l g g' P)
structure Lat (ι : Type) (n : ℕ) (O : Type) [CommRing O] where
  P : ι → Matrix (Fin n) (Fin n) O⟦X⟧
  D : ι → Matrix (Fin n) (Fin n) O⟦X⟧
  Th : ι → Matrix (Fin n) (Fin n) O
def LatW {ι : Type} {n : ℕ} {O : Type} [CommRing O] (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O]
    (N : Lat ι n O) (h : ℕ) (u : ℤ_[l]ˣ) (U' : ι → Fin n → ℤ) : Prop :=
  (∀ i, ∃ M : Matrix (Fin n) (Fin n) O⟦X⟧,
    N.P i * M = ((X - C (l : O)) ^ h) • (1 : Matrix (Fin n) (Fin n) O⟦X⟧)) ∧
  (∀ i (r S : ℕ), (∀ J : Finset (Fin n), J.card = r → (S : ℤ) ≤ ∑ j ∈ J, U' i j) →
    MinorsDvd ((X - C (l : O)) ^ S) r (N.P i)) ∧
  (∀ i, ∃ v : (O⟦X⟧)ˣ, (N.P i).det = (v : O⟦X⟧) * (X - C (l : O)) ^ (∑ j, U' i j).toNat) ∧
  (∀ i a b, (X - C (l : O)) ∣ N.D i a b - C (N.Th i a b)) ∧
  (∀ i, ∃ r : Fin n → ℤ_[l],
    (∀ j, ((u ^ (-(U' i j)) : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) * r j) ∧
    (N.Th i).charpoly = ∏ j, (Polynomial.X - Polynomial.C (algebraMap ℤ_[l] O (r j))))
def RankOneModel : Prop :=
  ∀ (ι : Type) (l h : ℕ) [Fact l.Prime] (O F : Type) [CommRing O] [Algebra ℤ_[l] O] [Field F]
    [CharP F l] (red : O →+* F) (N : Lat ι 1 O) (u : ℤ_[l]ˣ) (c : ℤ_[l]) (wt : ι → ℤ),
    (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c → LatW l N h u (fun i _ => wt i) →
    ∀ i, (∃ v : (O⟦X⟧)ˣ, N.P i 0 0 = (v : O⟦X⟧) * (X - C (l : O)) ^ (wt i).toNat) ∧
      red (constantCoeff (N.D i 0 0)) = -red (algebraMap ℤ_[l] O c) * ((wt i : ℤ) : F)
structure WLat (ι : Type) (t n : ℕ) (O F : Type) [CommRing O] [Field F] where
  red : O →+* F
  un : O⟦X⟧
  N : Lat ι n O
  Npsi : Fin t → Lat ι 1 O
  g : ι → (Matrix (Fin n) (Fin n) F⟦X⟧)ˣ
  b : Fin n → ℕ
  pos : Fin t → Fin n
  w : ι → Fin t → (F⟦X⟧)ˣ
section WLat
variable {ι : Type} {t n : ℕ} {O F : Type} [CommRing O] [Field F]
def WLat.unbar (W : WLat ι t n O F) : F⟦X⟧ := PowerSeries.map W.red W.un
def WLat.Gam (W : WLat ι t n O F) (i : ι) : Matrix (Fin n) (Fin n) F⟦X⟧ :=
  chgGam W.unbar (W.g i) ((W.N.D i).map (PowerSeries.map W.red))
def WLat.Phi (W : WLat ι t n O F) (l : ℕ) (σ : Equiv.Perm ι) (i : ι) :
    Matrix (Fin n) (Fin n) F⟦X⟧ :=
  chgPhi l (W.g i) (W.g (σ i)) ((W.N.P i).map (PowerSeries.map W.red))
def WLat.toWData (W : WLat ι t n O F) (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] (c : ℤ_[l])
    (σ : Equiv.Perm ι) : WData ι t n F where
  a := W.red (algebraMap ℤ_[l] O c)
  Θ i := thetaOf (W.Gam i)
  Φ i := W.Phi l σ i
  b := W.b
  pos := W.pos
def WFrame (W : WLat ι t n O F) (σ : Equiv.Perm ι) (l h : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O]
    (u : ℤ_[l]ˣ) (c : ℤ_[l]) (U' : ι → Fin n → ℤ) (wt kap : ι → Fin t → ℤ) : Prop :=
  ((u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c ∧ IsUnit c ∧ IsUn l O (u : ℤ_[l]) W.un) ∧
  (∀ i j, 0 ≤ U' i j ∧ U' i j ≤ (h : ℤ)) ∧ (∀ i s, 0 ≤ wt i s ∧ wt i s ≤ (h : ℤ)) ∧
  (Function.Injective W.pos ∧ ∀ s j, W.b j = W.b (W.pos s) → j = W.pos s) ∧
  (∀ i, (W.Phi l σ i).BlockTriangular W.b) ∧ (∀ i, (W.Gam i).BlockTriangular W.b) ∧
  (∀ i s,
    ((frob0 l (W.w (σ i) s : F⟦X⟧) : F⟦X⟧) : LaurentSeries F) *
        ((X : F⟦X⟧) : LaurentSeries F) ^ ((l : ℤ) * kap (σ i) s) *
        ((PowerSeries.map W.red ((W.Npsi s).P i 0 0) : F⟦X⟧) : LaurentSeries F) =
      ((W.Phi l σ i (W.pos s) (W.pos s) : F⟦X⟧) : LaurentSeries F) *
        ((W.w i s : F⟦X⟧) : LaurentSeries F) * ((X : F⟦X⟧) : LaurentSeries F) ^ kap i s) ∧
  (∀ i s,
    ((gam0 0 W.unbar (W.w i s : F⟦X⟧) : F⟦X⟧) : LaurentSeries F) *
        ((gamSer 0 W.unbar : F⟦X⟧) : LaurentSeries F) ^ kap i s *
        ((1 + X * PowerSeries.map W.red ((W.Npsi s).D i 0 0) : F⟦X⟧) : LaurentSeries F) =
      ((W.Gam i (W.pos s) (W.pos s) : F⟦X⟧) : LaurentSeries F) *
        ((W.w i s : F⟦X⟧) : LaurentSeries F) * ((X : F⟦X⟧) : LaurentSeries F) ^ kap i s)
def WInputs (W : WLat ι t n O F) (σ : Equiv.Perm ι) (l h : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O]
    (u : ℤ_[l]ˣ) (c : ℤ_[l]) (U' : ι → Fin n → ℤ) (wt kap : ι → Fin t → ℤ) : Prop :=
  WFrame W σ l h u c U' wt kap ∧ LatW l W.N h u U' ∧
    ∀ s, LatW l (W.Npsi s) h u (fun i _ => wt i s)
end WLat
def AlphaBounds : Prop :=
  ∀ (ι : Type) [Fintype ι] (σ : Equiv.Perm ι) (l h t n : ℕ) [Fact l.Prime] (O F : Type) [CommRing O]
    [IsDomain O] [Algebra ℤ_[l] O] [Field F] [CharP F l] (W : WLat ι t n O F) (u : ℤ_[l]ˣ)
    (c : ℤ_[l]) (U' : ι → Fin n → ℤ) (wt kap : ι → Fin t → ℤ),
    l ≠ 2 → WInputs W σ l h u c U' wt kap →
    ∀ i s, 0 ≤ (l : ℤ) * kap (σ i) s + wt i s - kap i s ∧
      (l : ℤ) * kap (σ i) s + wt i s - kap i s ≤ (h : ℤ)
def WPropsOfInputs : Prop :=
  ∀ (ι : Type) [Fintype ι] (σ : Equiv.Perm ι) (l h t n : ℕ) [Fact l.Prime] (O F : Type) [CommRing O]
    [IsDomain O] [Algebra ℤ_[l] O] [Field F] [CharP F l] (W : WLat ι t n O F) (u : ℤ_[l]ˣ)
    (c : ℤ_[l]) (U' : ι → Fin n → ℤ) (bot : ι → ℤ) (kap : ι → Fin t → ℤ) (cc : ι → ℕ),
    l ≠ 2 → WInputs W σ l h u c U' (fun i s => bot i + ((s : ℕ) : ℤ)) kap →
    (∀ i (J : Finset (Fin n)), J.card = t → (cc i : ℤ) ≤ ∑ j ∈ J, U' i j) →
    WProps (W.toWData l c σ) σ l U' bot kap cc
def LemmaWFromInputs : Prop :=
  ∀ (ι : Type) [Fintype ι] (σ : Equiv.Perm ι) (l h t n : ℕ) [Fact l.Prime] (O F : Type) [CommRing O]
    [IsDomain O] [Algebra ℤ_[l] O] [Field F] [CharP F l] (W : WLat ι t n O F) (u : ℤ_[l]ˣ)
    (c : ℤ_[l]) (U' : ι → Fin n → ℤ) (bot : ι → ℤ) (kap : ι → Fin t → ℤ),
    l ≠ 2 → WInputs W σ l h u c U' (fun i s => bot i + ((s : ℕ) : ℤ)) kap →
    (∀ i s, ((l : ℤ) - 1) * |kap i s| ≤ (h : ℤ)) ∧
    (∀ i, Multiset.map (fun s : Fin t => ((bot i + ((s : ℕ) : ℤ) - kap i s : ℤ) : ZMod l))
        Finset.univ.val ≤ Multiset.map (fun j => ((U' i j : ℤ) : ZMod l)) Finset.univ.val) ∧
    (∀ i, ∃ J : Finset (Fin n), J.card = t ∧
      ∑ j ∈ J, U' i j ≤ ∑ s : Fin t, (bot i + ((s : ℕ) : ℤ) + (l : ℤ) * kap (σ i) s - kap i s))
def LemmaWFull : Prop :=
  ∀ (ι : Type) [Fintype ι] (σ : Equiv.Perm ι) (l h t n : ℕ) [Fact l.Prime] (O F : Type) [CommRing O]
    [IsDomain O] [Algebra ℤ_[l] O] [Field F] [CharP F l] (W : WLat ι t n O F) (u : ℤ_[l]ˣ)
    (c : ℤ_[l]) (U' : ι → Fin n → ℤ) (wt kap : ι → Fin t → ℤ),
    l ≠ 2 → WInputs W σ l h u c U' wt kap →
    (∀ i s, ((l : ℤ) - 1) * |kap i s| ≤ (h : ℤ)) ∧
    (∀ i, Multiset.map (fun s : Fin t => ((wt i s - kap i s : ℤ) : ZMod l))
        Finset.univ.val ≤ Multiset.map (fun j => ((U' i j : ℤ) : ZMod l)) Finset.univ.val) ∧
    (∀ (ν : ℕ → ℕ),
      (∀ r ∈ Finset.univ.image W.b \ Finset.univ.image (fun s => W.b (W.pos s)),
        ν r ≤ (Finset.univ.filter fun j => W.b j = r).card) →
      ∀ i, ∃ J : Finset (Fin n),
        J.card = t + ∑ r ∈ Finset.univ.image W.b \ Finset.univ.image (fun s => W.b (W.pos s)), ν r ∧
        ∑ j ∈ J, U' i j ≤ ∑ s : Fin t, (wt i s + (l : ℤ) * kap (σ i) s - kap i s) +
          ((∑ r ∈ Finset.univ.image W.b \ Finset.univ.image (fun s => W.b (W.pos s)), ν r : ℕ) : ℤ) * h)
def WEFromInputs : Prop :=
  ∀ (ι : Type) [Fintype ι] (σ : Equiv.Perm ι) (k j t q l h : ℕ) [Fact l.Prime] (O F : Type)
    [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [Field F] [CharP F l]
    (W : WLat ι t (k + j + t + q) O F) (u : ℤ_[l]ˣ) (c : ℤ_[l])
    (U U' : ι → Fin (k + j + t + q) → ℤ) (bot cst : ι → ℤ) (kap : ι → Fin t → ℤ) (τ : ι),
    l ≠ 2 → t + 2 * (h / (l - 1)) < l →
    WInputs W σ l h u c U' (fun i s => bot i + ((s : ℕ) : ℤ)) kap →
    (∀ i, StrictAnti (U i)) → (∀ i, StrictAnti (U' i)) →
    (∀ i (s : Fin t), ∃ a, U i a = bot i + ((s : ℕ) : ℤ)) →
    (∀ i, (∏ a, (Polynomial.X + Polynomial.C (((U i a + cst i : ℤ)) : F))) =
      ∏ a, (Polynomial.X + Polynomial.C (((U' i a + cst i : ℤ)) : F))) →
    (∀ a, 0 ≤ U τ a) → ∑ a, U τ a = ∑ a, U' τ a →
    (∀ a : Fin (k + j + t + q), k + j ≤ (a : ℕ) → (a : ℕ) < k + j + t →
      U τ a = bot τ + ((k + j + t - 1 - (a : ℕ) : ℕ) : ℤ)) →
    ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < k + j), (U τ a - U' τ a) ≤
      (q : ℤ) * h +
        ((l : ℤ) * (mwCount l (bot (σ τ)) t (h / (l - 1)) (Finset.univ.image (U (σ τ))) : ℤ) +
          (mwCount l (bot τ) t (h / (l - 1)) (Finset.univ.image (U τ)) : ℤ)) *
          ((t : ℤ) + 2 * ((h / (l - 1) : ℕ) : ℤ))
def OrderDescent : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (I : Ideal O) [IsAdicComplete I O] (x : O) (L : Type)
    [CommRing L] [IsDomain L] (em : O →+* L) (jj : O⟦X⟧ →+* L⟦X⟧), x ∈ I → Function.Injective em →
    (∀ a, jj (C a) = C (em a)) → Associated (jj (X - C x)) X →
    ∀ (S : ℕ) (m : O⟦X⟧), (X : L⟦X⟧) ^ S ∣ jj m → (X - C x) ^ S ∣ m
def IsLocExp (l : ℕ) [Fact l.Prime] (O L : Type) [CommRing O] [Algebra ℤ_[l] O] [Field L]
    (em : O →+* L) (x : O) (u : ℤ_[l]) (jj : O⟦X⟧ →+* L⟦X⟧) : Prop :=
  (∀ a, jj (C a) = C (em a)) ∧ Associated (jj (X - C x)) X ∧
  (∀ f, jj (act l O u f) = rescale (em (algebraMap ℤ_[l] O u)) (jj f))
def LocFacts : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O L : Type) [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [Field L]
    (I : Ideal O) (ζ : O) (em : O →+* L) (u : ℤ_[l]) (b : ℕ) (jj : O⟦X⟧ →+* L⟦X⟧), l ≠ 2 →
    IsPrimitiveRoot ζ l → ζ - 1 ∈ I → Function.Injective em → b ∈ Finset.Ioo 0 l →
    IsLocExp l O L em (ζ ^ b - 1) u jj →
    (l : O) ∈ I ∧ (l : O) ≠ 0 ∧ Associated (jj (q0 l O)) X ∧
    ∀ (y : O⟦X⟧) (a : O), (X - C (l : O)) ∣ y - C a → constantCoeff (jj (inc l O y)) = em a
def LatN {ι : Type} {n : ℕ} {O L : Type} [CommRing O] [Field L] (l : ℕ) [Fact l.Prime]
    [Algebra ℤ_[l] O] (N : Lat ι n O) (h : ℕ) (u : ℤ_[l]ˣ) (U' : ι → Fin n → ℤ) (em : O →+* L)
    (jj : ℕ → O⟦X⟧ →+* L⟦X⟧) : Prop :=
  (∀ i, ∃ Q : Matrix (Fin n) (Fin n) O⟦X⟧,
    (N.P i).map (inc l O) * Q = (q l O ^ h) • (1 : Matrix (Fin n) (Fin n) O⟦X⟧)) ∧
  (∀ i a b, (X - C (l : O)) ∣ N.D i a b - C (N.Th i a b)) ∧
  (∀ i, ∀ b ∈ Finset.Ioo 0 l, ∃ G H : (Matrix (Fin n) (Fin n) L⟦X⟧)ˣ,
    (N.P i).map (fun y => jj b (inc l O y)) =
      (G : Matrix (Fin n) (Fin n) L⟦X⟧) * Matrix.diagonal (fun a => (X : L⟦X⟧) ^ (U' i a).toNat) *
        (H : Matrix (Fin n) (Fin n) L⟦X⟧) ∧
    ((1 + (X : O⟦X⟧) • N.D i).map (fun y => jj b (inc l O y))) *
        ((G : Matrix (Fin n) (Fin n) L⟦X⟧) *
          Matrix.diagonal (fun a => (X : L⟦X⟧) ^ (U' i a).toNat)).map
          (rescale (em (algebraMap ℤ_[l] O (u : ℤ_[l])))) =
      (G : Matrix (Fin n) (Fin n) L⟦X⟧) * Matrix.diagonal (fun a => (X : L⟦X⟧) ^ (U' i a).toNat))
def LatWOfN : Prop :=
  ∀ (ι : Type) (l h n : ℕ) [Fact l.Prime] (O L : Type) [CommRing O] [IsDomain O] [Algebra ℤ_[l] O]
    [Field L] (I : Ideal O) [IsAdicComplete I O] (ζ : O) (em : O →+* L)
    (jj : ℕ → O⟦X⟧ →+* L⟦X⟧) (N : Lat ι n O) (u : ℤ_[l]ˣ) (c : ℤ_[l]) (U' : ι → Fin n → ℤ), l ≠ 2 →
    (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c → IsPrimitiveRoot ζ l → ζ - 1 ∈ I → Function.Injective em →
    (∀ b ∈ Finset.Ioo 0 l, IsLocExp l O L em (ζ ^ b - 1) (u : ℤ_[l]) (jj b)) →
    (∀ i a, 0 ≤ U' i a) → LatN l N h u U' em jj → LatW l N h u U'
def NInputs {ι : Type} {t n : ℕ} {O F L : Type} [CommRing O] [Field F] [Field L]
    (W : WLat ι t n O F) (σ : Equiv.Perm ι) (l h : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O]
    (u : ℤ_[l]ˣ) (c : ℤ_[l]) (U' : ι → Fin n → ℤ) (wt kap : ι → Fin t → ℤ) (I : Ideal O) (ζ : O)
    (em : O →+* L) (jj : ℕ → O⟦X⟧ →+* L⟦X⟧) : Prop :=
  WFrame W σ l h u c U' wt kap ∧
  (IsPrimitiveRoot ζ l ∧ ζ - 1 ∈ I ∧ Function.Injective em ∧
    ∀ b ∈ Finset.Ioo 0 l, IsLocExp l O L em (ζ ^ b - 1) (u : ℤ_[l]) (jj b)) ∧
  LatN l W.N h u U' em jj ∧ ∀ s, LatN l (W.Npsi s) h u (fun i _ => wt i s) em jj
def WInputsOfN : Prop :=
  ∀ (ι : Type) (σ : Equiv.Perm ι) (l h t n : ℕ) [Fact l.Prime] (O F L : Type) [CommRing O]
    [IsDomain O] [Algebra ℤ_[l] O] [Field F] [Field L] (I : Ideal O) [IsAdicComplete I O]
    (W : WLat ι t n O F) (u : ℤ_[l]ˣ) (c : ℤ_[l]) (U' : ι → Fin n → ℤ) (wt kap : ι → Fin t → ℤ)
    (ζ : O) (em : O →+* L) (jj : ℕ → O⟦X⟧ →+* L⟦X⟧), l ≠ 2 →
    NInputs W σ l h u c U' wt kap I ζ em jj → WInputs W σ l h u c U' wt kap
def LemmaWFromLattice : Prop :=
  ∀ (ι : Type) [Fintype ι] (σ : Equiv.Perm ι) (l h t n : ℕ) [Fact l.Prime] (O F L : Type) [CommRing O]
    [IsDomain O] [Algebra ℤ_[l] O] [Field F] [CharP F l] [Field L] (I : Ideal O) [IsAdicComplete I O]
    (W : WLat ι t n O F) (u : ℤ_[l]ˣ) (c : ℤ_[l]) (U' : ι → Fin n → ℤ) (wt kap : ι → Fin t → ℤ)
    (ζ : O) (em : O →+* L) (jj : ℕ → O⟦X⟧ →+* L⟦X⟧),
    l ≠ 2 → NInputs W σ l h u c U' wt kap I ζ em jj →
    (∀ i s, 0 ≤ (l : ℤ) * kap (σ i) s + wt i s - kap i s ∧
      (l : ℤ) * kap (σ i) s + wt i s - kap i s ≤ (h : ℤ)) ∧
    (∀ i s, ((l : ℤ) - 1) * |kap i s| ≤ (h : ℤ)) ∧
    (∀ i, Multiset.map (fun s : Fin t => ((wt i s - kap i s : ℤ) : ZMod l))
        Finset.univ.val ≤ Multiset.map (fun j => ((U' i j : ℤ) : ZMod l)) Finset.univ.val) ∧
    (∀ (ν : ℕ → ℕ),
      (∀ r ∈ Finset.univ.image W.b \ Finset.univ.image (fun s => W.b (W.pos s)),
        ν r ≤ (Finset.univ.filter fun j => W.b j = r).card) →
      ∀ i, ∃ J : Finset (Fin n),
        J.card = t + ∑ r ∈ Finset.univ.image W.b \ Finset.univ.image (fun s => W.b (W.pos s)), ν r ∧
        ∑ j ∈ J, U' i j ≤ ∑ s : Fin t, (wt i s + (l : ℤ) * kap (σ i) s - kap i s) +
          ((∑ r ∈ Finset.univ.image W.b \ Finset.univ.image (fun s => W.b (W.pos s)), ν r : ℕ) : ℤ) * h)
def WEFromLattice : Prop :=
  ∀ (ι : Type) [Fintype ι] (σ : Equiv.Perm ι) (k j t q l h : ℕ) [Fact l.Prime] (O F L : Type)
    [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [Field F] [CharP F l] [Field L] (I : Ideal O)
    [IsAdicComplete I O] (W : WLat ι t (k + j + t + q) O F) (u : ℤ_[l]ˣ) (c : ℤ_[l])
    (U U' : ι → Fin (k + j + t + q) → ℤ) (bot cst : ι → ℤ) (kap : ι → Fin t → ℤ) (τ : ι)
    (ζ : O) (em : O →+* L) (jj : ℕ → O⟦X⟧ →+* L⟦X⟧),
    l ≠ 2 → t + 2 * (h / (l - 1)) < l →
    NInputs W σ l h u c U' (fun i s => bot i + ((s : ℕ) : ℤ)) kap I ζ em jj →
    (∀ i, StrictAnti (U i)) → (∀ i, StrictAnti (U' i)) →
    (∀ i (s : Fin t), ∃ a, U i a = bot i + ((s : ℕ) : ℤ)) →
    (∀ i, (∏ a, (Polynomial.X + Polynomial.C (((U i a + cst i : ℤ)) : F))) =
      ∏ a, (Polynomial.X + Polynomial.C (((U' i a + cst i : ℤ)) : F))) →
    (∀ a, 0 ≤ U τ a) → ∑ a, U τ a = ∑ a, U' τ a →
    (∀ a : Fin (k + j + t + q), k + j ≤ (a : ℕ) → (a : ℕ) < k + j + t →
      U τ a = bot τ + ((k + j + t - 1 - (a : ℕ) : ℕ) : ℤ)) →
    ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < k + j), (U τ a - U' τ a) ≤
      (q : ℤ) * h +
        ((l : ℤ) * (mwCount l (bot (σ τ)) t (h / (l - 1)) (Finset.univ.image (U (σ τ))) : ℤ) +
          (mwCount l (bot τ) t (h / (l - 1)) (Finset.univ.image (U τ)) : ℤ)) *
          ((t : ℤ) + 2 * ((h / (l - 1) : ℕ) : ℤ))
end Formalism.CohomologicalDescent.FrobeniusPeriodChange


