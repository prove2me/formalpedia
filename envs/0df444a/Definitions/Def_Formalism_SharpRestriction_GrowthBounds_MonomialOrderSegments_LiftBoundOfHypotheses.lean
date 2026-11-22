-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_LiftBoundOfHypotheses
-- name    : Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_LiftBoundOfHypotheses
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:25:14.750808+00:00
-- url     : https://prove2.me/theorems/87d29662-f792-4df6-88de-de278dd47ff7
-- title:
--   Lift Bound Of Hypotheses
-- statement:
--   Definitions and structural lemmas for Lift Bound Of Hypotheses, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/LiftBoundOfHypotheses.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
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
namespace Formalism.MainNotions.PlaneGram
section Basic
variable {K : Type} [Field K]
def vR (v : AddValuation K (WithTop ℚ)) (x : K) : WithTop ℝ := (v x).map (fun n : ℚ => (n : ℝ))
def toR (x : WithTop ℤ) : WithTop ℝ := x.map (fun n : ℤ => (n : ℝ))
structure DVRHyp (v : AddValuation K (WithTop ℚ)) (p : ℕ) : Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  vp : v (p : K) = 1
def lg (p r a : ℕ) : ℝ := Real.logb p ((a : ℝ) + r) + 1
def fact {σ : Type} (α : σ →₀ ℕ) : ℕ := α.prod fun _ k => k.factorial
def absE {σ : Type} (α : σ →₀ ℕ) : ℕ := α.sum fun _ k => k
def PolK {L : Type} (K : Type) [Field K] (r : ℕ) (d : L → ℕ) :
    Submodule K (MvPolynomial (L × Fin r) K) :=
  restrictSupport K {α | ∀ i, ∑ a : Fin r, α (i, a) = d i}
def Integral (v : AddValuation K (WithTop ℚ)) {σ : Type} (F : MvPolynomial σ K) : Prop :=
  ∀ α, 0 ≤ v (F.coeff α)
def PolO {L : Type} (v : AddValuation K (WithTop ℚ)) (r : ℕ) (d : L → ℕ) :
    Set (MvPolynomial (L × Fin r) K) :=
  {F | F ∈ PolK K r d ∧ Integral v F}
def fock {σ : Type} (F G : MvPolynomial σ K) : K :=
  ∑ α ∈ F.support, F.coeff α * G.coeff α * (fact α : K)
def vBB (v : AddValuation K (WithTop ℚ)) {σ : Type} (F : MvPolynomial σ K) : WithTop ℝ :=
  F.support.inf fun α => vR v (F.coeff α) + ((((v (fact α : K)).untopD 0 : ℚ) : ℝ) / 2 : ℝ)
def kap (p r : ℕ) {L : Type} [Fintype L] (d : L → ℕ) : ℝ := ∑ i, (r : ℝ) * lg p r (d i)
def binomComb {σ : Type} [Fintype σ] (T : Finset (σ → ℕ)) (lam : (σ → ℕ) → K) (β : σ → ℕ) : K :=
  ∑ m ∈ T, lam m * ∏ x, ((β x).choose (m x) : K)
end Basic
section Val
variable (K : Type) [Field K]
abbrev GenF (r : ℕ) := Formalism.MainNotions.G.GLCoord K r
abbrev LauF (r : ℕ) := LaurentPolynomial (GenF K r)
def sDiag (r : ℕ) (n : ℤ) : Matrix (Fin r) (Fin r) (LauF K r) :=
  Matrix.diagonal fun a => if a.val + 1 = r then LaurentPolynomial.T n else 1
def hMat (r : ℕ) : Matrix (Fin r) (Fin r) (LauF K r) :=
  (Formalism.MainNotions.G.gL K r * sDiag K r 1 * Formalism.MainNotions.G.gLinv K r).transpose
def hInvT (r : ℕ) : Matrix (Fin r) (Fin r) (LauF K r) :=
  Formalism.MainNotions.G.gL K r * sDiag K r (-1) * Formalism.MainNotions.G.gLinv K r
def lauι (r : ℕ) : K →+* LauF K r := Formalism.MainNotions.G.coefL K r
variable {K}
def substS {L : Type} [DecidableEq L] {r : ℕ} {R : Type} [CommRing R] (ι : K →+* R)
    (sg : L → Bool) (S : Finset L) (A B : Matrix (Fin r) (Fin r) R) :
    MvPolynomial (L × Fin r) K →+* MvPolynomial (L × Fin r) R :=
  eval₂Hom ((MvPolynomial.C).comp ι) fun x =>
    if x.1 ∈ S then
      (if sg x.1 then ∑ b, MvPolynomial.C (A x.2 b) * X (x.1, b)
       else ∑ b, MvPolynomial.C (B x.2 b) * X (x.1, b))
    else X x
def lord {R : Type} [Semiring R] (f : LaurentPolynomial R) : WithTop ℤ := f.coeff.support.min
def valS {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L)
    (F : MvPolynomial (L × Fin r) K) : WithTop ℤ :=
  let G := substS (lauι K r) sg S (hMat K r) (hInvT K r) F
  G.support.inf fun β => lord (G.coeff β)
def Aset {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L) (th : ℤ) :
    Set (MvPolynomial (L × Fin r) K) :=
  {F | (th : WithTop ℤ) ≤ valS sg S F}
end Val
section Act
variable {K : Type} [Field K]
def lastIdx (r : ℕ) [NeZero r] : Fin r := ⟨r - 1, by have := NeZero.pos r; omega⟩
def ddiv {σ : Type} (M : σ →₀ ℕ) (F : MvPolynomial σ K) : MvPolynomial σ K :=
  ∑ α ∈ F.support, if M ≤ α then monomial (α - M) (F.coeff α * α.prod fun x k => (k.choose (M x) : K)) else 0
def onLetter {L : Type} {r : ℕ} (i : L) (β : Fin r →₀ ℕ) : L × Fin r →₀ ℕ :=
  Finsupp.mapDomain (fun a => (i, a)) β
end Act
section Admitted
variable (K : Type) [Field K]
def V2 [CharZero K] : Prop :=
  ∀ (L : Type) [Fintype L] [DecidableEq L] (sg : L → Bool) (r : ℕ) [NeZero r] (S : Finset L),
    (∀ (i : L) (a : Fin r),
      ((if sg i then 0 else -1 : ℤ) : WithTop ℤ) ≤ valS sg S (X (i, a) : MvPolynomial (L × Fin r) K)) ∧
    (∀ (i : L) (β : Fin r →₀ ℕ) (F : MvPolynomial (L × Fin r) K),
      valS sg S F + (((if sg i then -(absE β : ℤ) else 0) : ℤ) : WithTop ℤ) ≤
        valS sg S (ddiv (onLetter i β) F)) ∧
    (∀ S' : Finset L, S ⊆ S' → (∀ i ∈ S', i ∉ S → sg i = true) →
      ∀ F : MvPolynomial (L × Fin r) K, valS sg S F ≤ valS sg S' F) ∧
    (∀ (d : L → ℕ) (S' : Finset L), S' ⊆ S → (∀ i ∈ S, i ∉ S' → sg i = true) →
      ∀ F ∈ PolK K r d, valS sg S F + ((-(∑ i ∈ S \ S', d i : ℕ) : ℤ) : WithTop ℤ) ≤ valS sg S' F)
def initSet (N : ℕ) (i : ℕ) : Finset (Fin N) := univ.filter fun k => k.val < i
def IsPieriStep {r : ℕ} (vec : Bool) (deg : ℕ) (μ ν : Fin r → ℤ) : Prop :=
  if vec then (∀ a, μ a ≤ ν a) ∧ (∀ a b : Fin r, b.val + 1 = a.val → ν a ≤ μ b) ∧
      ∑ a, ν a = ∑ a, μ a + deg
  else (∀ a, ν a ≤ μ a) ∧ (∀ a b : Fin r, b.val + 1 = a.val → μ a ≤ ν b) ∧
      ∑ a, μ a = ∑ a, ν a + deg
def IsPieriPath {N r : ℕ} (sg : Fin N → Bool) (d : Fin N → ℕ) (path : Fin (N + 1) → Fin r → ℤ) : Prop :=
  path 0 = 0 ∧ ∀ k : Fin N, IsPieriStep (sg k) (d k) (path k.castSucc) (path k.succ)
variable (v : AddValuation K (WithTop ℚ)) (p : ℕ)
def colVal (ci : ℤ) (h r : ℕ) : ℤ :=
  (if 1 ≤ ci ∧ h = r then 1 else 0) - (if ci ≤ 0 ∧ h < r then 1 else 0)
def SPAN [CharZero K] : Prop :=
  DVRHyp v p → ∀ (N r : ℕ) [NeZero r] (sg : Fin N → Bool) (d : Fin N → ℕ),
  ∃ (ι : Type) (_ : Fintype ι) (Ψ : ι → MvPolynomial (Fin N × Fin r) K)
    (path : ι → Fin (N + 1) → Fin r → ℤ) (ncol : ι → ℕ)
    (col : (b : ι) → Fin (ncol b) → MvPolynomial (Fin N × Fin r) K)
    (cidx : (b : ι) → Fin (ncol b) → ℤ) (hts : (b : ι) → Fin (ncol b) → Fin (N + 1) → ℕ)
    (occ : (b : ι) → Fin (ncol b) → Finset (Fin N)),
    (∀ b, Ψ b ∈ PolO v r d) ∧ LinearIndependent K Ψ ∧
    (∀ F ∈ PolO v r d, ∃ c : ι → K, (∀ b, 0 ≤ v (c b)) ∧ F = ∑ b, c b • Ψ b) ∧
    (∀ (th : Fin (N + 1) → ℤ) (F : MvPolynomial (Fin N × Fin r) K),
      (F ∈ PolO v r d ∧ ∀ i : Fin (N + 1), F ∈ Aset sg (initSet N i.val) (th i)) →
        ∃ c : ι → K, (∀ b, 0 ≤ v (c b)) ∧ (∀ b, c b ≠ 0 → ∀ i, th i ≤ path b i (lastIdx r)) ∧
          F = ∑ b, c b • Ψ b) ∧
    (∀ b, Ψ b = ∏ k, col b k) ∧
    (∀ b k, col b k ∈ PolK K r (fun i => if i ∈ occ b k then 1 else 0)) ∧
    (∀ b i, (univ.filter fun k => i ∈ occ b k).card = d i) ∧
    (∀ b k (i : Fin (N + 1)), 1 ≤ cidx b k →
      hts b k i ≤ ((occ b k).filter fun l => l.val < i.val ∧ sg l = true).card) ∧
    (∀ b k (i : Fin (N + 1)),
      ((colVal (cidx b k) (hts b k i) r : ℤ) : WithTop ℤ) ≤ valS sg (initSet N i.val) (col b k)) ∧
    (∀ b (i : Fin (N + 1)), path b i (lastIdx r) = ∑ k, colVal (cidx b k) (hts b k i) r)
def IsFockProj {L : Type} {r : ℕ} (d : L → ℕ) (W : Set (MvPolynomial (L × Fin r) K))
    (π : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K) : Prop :=
  ∀ F ∈ PolK K r d, π F ∈ PolK K r d ∧ π F ∈ W ∧ (F ∈ W → π F = F) ∧
    ∀ G ∈ PolK K r d, G ∈ W → fock (F - π F) G = 0
def PROJ [CharZero K] (_C0 : ℝ) : Prop :=
  DVRHyp v p → ∀ (L : Type) [Fintype L] [DecidableEq L] (sg : L → Bool) (r : ℕ) [NeZero r] (d : L → ℕ)
    (S : Finset L) (th : ℤ),
    (∃ π, IsFockProj (K := K) (r := r) d (Aset sg S th) π) ∧
    ∀ π, IsFockProj (K := K) (r := r) d (Aset sg S th) π →
      (∀ i : L, sg i = true → i ∉ S → ∀ (a : Fin r), ∀ F ∈ PolK K r d,
          π (X (i, a) * pderiv (i, a) F) = X (i, a) * pderiv (i, a) (π F)) ∧
      (∀ S' : Finset L, (S ⊆ S' ∨ Disjoint S S') →
        ∀ (th' : ℤ) (π'), IsFockProj (K := K) (r := r) d (Aset sg S' th') π' → ∀ F ∈ PolK K r d,
          π (π' F) = π' (π F)) ∧
      ∀ F ∈ PolK K r d,
        vBB v F ≤ vBB v (π F) + (((r : ℝ) ^ 2 * lg p r (2 * ∑ i, d i) : ℝ) : WithTop ℝ)
def DIG [CharZero K] : Prop :=
  DVRHyp v p → ∀ (τ : Type) [Fintype τ] (r : ℕ) (g : τ → ℕ),
    ∃ (const : τ → (Fin r → ℕ) → ℕ → K) (gam : τ → (Fin r → ℕ) → (Fin r → ℕ) → K),
      (∀ (t : τ) (ρ : Fin r → ℕ), (∀ a, ρ a < p ^ g t) →
        (∀ n, const t ρ n ≠ 0) ∧
        ∀ β : Fin r → ℕ, v (gam t ρ β) = 0 ∧
          ((∏ a, (ρ a + p ^ g t * β a).factorial : ℕ) : K) =
            const t ρ (∑ a, β a) * ((∏ a, (β a).factorial : ℕ) : K) * gam t ρ β) ∧
      ∀ ρ : τ → Fin r → ℕ, (∀ t a, ρ t a < p ^ g t) → ∀ c : ℕ, 1 ≤ c → ∀ ε : ℤ, (ε = 1 ∨ ε = -1) →
        ∃ (T : Finset (τ × Fin r → ℕ)) (lam : (τ × Fin r → ℕ) → K),
          (∀ m ∈ T, 0 ≤ v (lam m) ∧ ∑ x, m x ≤ 6 * c) ∧
          ∀ β : τ × Fin r → ℕ, ((c : ℕ) : WithTop ℚ) ≤
            v ((∏ t, gam t (ρ t) (fun a => β (t, a))) ^ ε - binomComb T lam β)
def DER [CharZero K] : Prop :=
  DVRHyp v p → ∀ (r g : ℕ) (ρ : Fin r →₀ ℕ), (∀ a, ρ a < p ^ g) → ∀ (M : Fin r →₀ ℕ) (c : ℕ), 1 ≤ c →
    ∃ (n : ℕ) (cf : Fin n → K) (ρ' δ κ : Fin n → (Fin r →₀ ℕ)),
      (∀ t, 0 ≤ v (cf t)) ∧
      (∀ t, (absE (κ t) : ℝ) ≤ (absE M : ℝ) / ((p : ℝ) ^ g) + c) ∧
      ∀ (β : Fin r →₀ ℕ) (γ : Fin r →₀ ℕ), ((c : ℕ) : WithTop ℚ) ≤
        v ((ddiv M (monomial (ρ + p ^ g • β) (1 : K)) -
          ∑ t, monomial (ρ' t) (cf t) *
            expand (p ^ g) (monomial (δ t) (1 : K) * ddiv (κ t) (monomial β (1 : K)))).coeff γ)
end Admitted
structure TwistData (K : Type) where
  r : ℕ
  J : ℕ
  Lb : Type
  [finLb : Fintype Lb]
  [decLb : DecidableEq Lb]
  seg : Lb → Fin J
  sgn : Lb → Bool
  dB : Lb → ℕ
  dT : Fin J × Fin r → ℕ
  g : Fin J × Fin r → ℕ
  nch : Fin J → ℕ
  chain : (j : Fin J) → Fin (nch j) → Finset Lb
  th : (j : Fin J) → Fin (nch j) → ℝ
  sl : (j : Fin J) → Fin (nch j) → ℝ
  thl : Fin J → Fin r → ℝ
  c : ℕ
  ga : ((Lb ⊕ (Fin J × Fin r)) × Fin r →₀ ℕ) → K
attribute [instance] TwistData.finLb TwistData.decLb
namespace TwistData
variable {K : Type} [Field K] (D : TwistData K)
abbrev Tau := Fin D.J × Fin D.r
abbrev OL := D.Lb ⊕ D.Tau
abbrev ML := D.Lb ⊕ (D.Tau ⊕ (D.Tau ⊕ D.Tau))
def mb (b : D.Lb) : D.ML := Sum.inl b
def mlab (t : D.Tau) : D.ML := Sum.inr (Sum.inl t)
def mw (t : D.Tau) : D.ML := Sum.inr (Sum.inr (Sum.inl t))
def mtp (t : D.Tau) : D.ML := Sum.inr (Sum.inr (Sum.inr t))
def osg : D.OL → Bool := Sum.elim D.sgn fun _ => true
def msg : D.ML → Bool := Sum.elim D.sgn fun _ => true
def dO : D.OL → ℕ := Sum.elim D.dB D.dT
def nxt (j : Fin D.J) : Fin D.J := ⟨(j.val + 1) % D.J, Nat.mod_lt _ j.pos⟩
def aux₃ (j : Fin D.J) : Fin D.J := ⟨(j.val + D.J - 1) % D.J, Nat.mod_lt _ j.pos⟩
def P (p : ℕ) (t : D.Tau) : ℕ := p ^ D.g t
def LLj (j : Fin D.J) : Finset D.Lb := univ.filter fun b => D.seg b = j
def dLL (j : Fin D.J) : ℕ := ∑ b ∈ D.LLj j, D.dB b
def totDeg : ℕ := ∑ i : D.OL, D.dO i
def eC (p : ℕ) (_C0 : ℝ) : ℝ := (D.r : ℝ) ^ 2 * lg p D.r (2 * D.totDeg)
def kapD (p : ℕ) : ℝ := kap p D.r D.dO
def Dm (p : ℕ) (C0 : ℝ) : ℝ := ∑ j, (D.nch j : ℝ) * D.eC p C0
def Dl (p : ℕ) (C0 : ℝ) : ℝ := (D.J : ℝ) * ((D.r : ℝ) - 1) * D.eC p C0
def n0 (v : AddValuation K (WithTop ℚ)) : ℝ :=
  (((v (((∏ i : D.OL, (D.dO i).factorial : ℕ) : K))).untopD 0 : ℚ) : ℝ) / 2
def ph (p : ℕ) : MvPolynomial (D.ML × Fin D.r) K →ₐ[K] MvPolynomial (D.OL × Fin D.r) K :=
  aeval fun x => Sum.elim (fun b => X (Sum.inl b, x.2))
    (Sum.elim (fun t => X (Sum.inr t, x.2))
      (Sum.elim (fun t => X (Sum.inr t, x.2) ^ D.P p t) (fun t => X (Sum.inr t, x.2)))) x.1
def InClass (p : ℕ) (ρ : D.Tau → Fin D.r → ℕ) (α : D.OL × Fin D.r →₀ ℕ) : Prop :=
  ∀ t a, α (Sum.inr t, a) % D.P p t = ρ t a
instance (p : ℕ) (ρ : D.Tau → Fin D.r → ℕ) (α : D.OL × Fin D.r →₀ ℕ) : Decidable (D.InClass p ρ α) := by
  unfold InClass; infer_instance
def liftE (p : ℕ) (α : D.OL × Fin D.r →₀ ℕ) : D.ML × Fin D.r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun x => Sum.elim (fun b => α (Sum.inl b, x.2))
    (Sum.elim (fun _ => 0) (Sum.elim (fun t => α (Sum.inr t, x.2) / D.P p t) (fun _ => 0))) x.1
def digitPart (p : ℕ) (ρ : D.Tau → Fin D.r → ℕ) (F : MvPolynomial (D.OL × Fin D.r) K) :
    MvPolynomial (D.ML × Fin D.r) K :=
  ∑ α ∈ F.support, if D.InClass p ρ α then monomial (D.liftE p α) (F.coeff α) else 0
def wSet (j : Fin D.J) : Finset D.ML := univ.image fun m : Fin D.r => D.mw (D.aux₃ j, m)
def chainSet (j : Fin D.J) (i : Fin (D.nch j)) : Finset D.ML := (D.chain j i).image D.mb ∪ D.wSet j
def Tset (j : Fin D.J) (m : Fin D.r) : Finset D.OL :=
  (D.LLj j).image Sum.inl ∪ (univ.filter fun m' : Fin D.r => m < m').image fun m' => Sum.inr (j, m')
def Yset (j : Fin D.J) (m : Fin D.r) : Finset D.ML :=
  D.wSet j ∪ (D.LLj j).image D.mb ∪ (univ.filter fun m' : Fin D.r => m < m').image fun m' => D.mtp (j, m')
def InXX (p : ℕ) (F : MvPolynomial (D.OL × Fin D.r) K) : Prop :=
  F ∈ PolK K D.r D.dO ∧
  (∀ (ρ : D.Tau → Fin D.r → ℕ) (j : Fin D.J) (i : Fin (D.nch j)),
    ((D.th j i : ℝ) : WithTop ℝ) ≤ toR (valS D.msg (D.chainSet j i) (D.digitPart p ρ F))) ∧
  ∀ (j : Fin D.J) (m : Fin D.r), m.val + 2 ≤ D.r →
    ((D.thl j m : ℝ) : WithTop ℝ) ≤ toR (valS D.osg (D.Tset j m) F)
def RRvars (G : MvPolynomial (D.ML × Fin D.r) K) : Prop :=
  ∀ α ∈ G.support, ∀ (j : Fin D.J) (m : Fin D.r), m.val = 0 → ∀ a, α (D.mtp (j, m), a) = 0
def InRR (v : AddValuation K (WithTop ℚ)) (G : MvPolynomial (D.ML × Fin D.r) K) : Prop :=
  Integral v G ∧ D.RRvars G
def InYY (v : AddValuation K (WithTop ℚ)) (k6 k18 : ℝ) (G : MvPolynomial (D.ML × Fin D.r) K) : Prop :=
  D.InRR v G ∧
  (∀ (j : Fin D.J) (i : Fin (D.nch j)),
    ((D.th j i - D.sl j i - k6 * D.c : ℝ) : WithTop ℝ) ≤ toR (valS D.msg (D.chainSet j i) G)) ∧
  ∀ (j : Fin D.J) (m : Fin D.r), m.val + 2 ≤ D.r →
    ((D.thl j m - k18 * D.c : ℝ) : WithTop ℝ) ≤ toR (valS D.msg (D.Yset j m) G)
def PhDeg (p : ℕ) (G : MvPolynomial (D.ML × Fin D.r) K) : Prop :=
  ∀ α ∈ G.support, (∀ b, ∑ a, α (D.mb b, a) = D.dB b) ∧
    ∀ t, ∑ a, (α (D.mlab t, a) + D.P p t * α (D.mw t, a) + α (D.mtp t, a)) = D.dT t
def gaAct (G : MvPolynomial (D.OL × Fin D.r) K) : MvPolynomial (D.OL × Fin D.r) K :=
  ∑ α ∈ G.support, monomial α (D.ga α * G.coeff α)
def GaOK (v : AddValuation K (WithTop ℚ)) (_p : ℕ) : Prop :=
  (∀ α, v (D.ga α) = 0) ∧
  ∀ ε : ℤ, (ε = 1 ∨ ε = -1) →
    ∃ (T : Finset (D.OL × Fin D.r → ℕ)) (lam : (D.OL × Fin D.r → ℕ) → K),
      (∀ m ∈ T, 0 ≤ v (lam m) ∧ ∑ x, m x ≤ 6 * D.c) ∧
      ∀ α : D.OL × Fin D.r →₀ ℕ,
        ((D.c : ℕ) : WithTop ℚ) ≤ v (D.ga α ^ ε - binomComb T lam (fun x => α x))
def Valid (v : AddValuation K (WithTop ℚ)) (p : ℕ) : Prop :=
  0 < D.r ∧ 0 < D.J ∧ 1 ≤ D.c ∧
  (∀ j i, D.chain j i ⊆ D.LLj j) ∧
  (∀ (j : Fin D.J) (i i' : Fin (D.nch j)), i < i' → D.chain j i ⊂ D.chain j i') ∧
  (∀ (j : Fin D.J) (m : Fin D.r), m.val + 2 ≤ D.r → 0 < D.thl j m) ∧
  D.GaOK v p
def HypH (p : ℕ) (kH : ℝ) : Prop :=
  ∀ (j : Fin D.J) (m : Fin D.r) (i : Fin (D.nch (D.nxt j))),
    (D.r : ℝ) * D.dLL j / (D.P p (j, m) : ℝ) + kH * D.r * D.c ≤ D.sl (D.nxt j) i
def Hc (p : ℕ) (C0 : ℝ) : Prop :=
  4 * (D.Dm p C0 + D.Dl p C0 + 3 * D.kapD p) < D.c
def E (p : ℕ) (C0 kE : ℝ) : ℝ := D.Dm p C0 + D.Dl p C0 + kE * D.kapD p
def LabLow (p : ℕ) (G : MvPolynomial (D.ML × Fin D.r) K) : Prop :=
  ∀ α ∈ G.support, ∀ (t : D.Tau) (a : Fin D.r), α (D.mlab t, a) < D.P p t
end TwistData
section Thm
variable (K : Type) [Field K] (v : AddValuation K (WithTop ℚ)) (p : ℕ)
open TwistData in

def LiftBoundWith [CharZero K] (C0 kH k6 k18 kE : ℝ) : Prop :=
  DVRHyp v p → ∀ D : TwistData K, D.Valid v p → D.HypH p kH → D.Hc p C0 →
    ∀ F : MvPolynomial (D.OL × Fin D.r) K, D.InXX p F → vBB v F = 0 →
      ∃ G' R : MvPolynomial (D.ML × Fin D.r) K,
        D.InYY v k6 k18 G' ∧ D.LabLow p G' ∧
        D.RRvars R ∧ D.LabLow p R ∧ (∀ α, ((D.c - D.E p C0 kE : ℝ) : WithTop ℝ) ≤ vR v (R.coeff α)) ∧
        D.PhDeg p G' ∧ D.PhDeg p R ∧
        ((D.n0 v - D.kapD p : ℝ) : WithTop ℝ) ≤ vBB v (D.ph p (G' + R)) ∧
        vR v (fock F (D.gaAct (D.ph p (G' + R)))) + ((-D.n0 v + D.kapD p : ℝ) : WithTop ℝ) ≤
          ((D.E p C0 kE + 2 * D.kapD p : ℝ) : WithTop ℝ)
def LiftBoundUniform [CharZero K] (C0 : ℝ) : Prop := LiftBoundWith K v p C0 13 12 30 2
def LiftBoundOfHypotheses [CharZero K] (C0 : ℝ) : Prop :=
  1 ≤ C0 → V2 K → SPAN K v p → PROJ K v p C0 → DIG K v p → DER K v p → LiftBoundUniform K v p C0
end Thm
end Formalism.MainNotions.PlaneGram


