-- Prove2me | Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
-- name    : Formalism_FormalDegreeBessel_StatementRP
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T13:29:46.248995+00:00
-- url     : https://prove2.me/theorems/5d383362-0b15-437e-b3cd-6932921a6a0a
-- title:
--   Statement RP
-- statement:
--   Definitions and structural lemmas for Statement RP, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/StatementRP.lean

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open MeasureTheory Matrix
noncomputable section
namespace Formalism.QuantumDeterminants
def levPos (k i r' : ℕ) (j : Fin (2 * r' + k + 1)) : Fin (2 * (i + r') + k + 1) := ⟨j.val + i, by omega⟩
def ιLev (k i r' : ℕ) (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ := fun p q =>
  if hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i then
    (if hq : i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i then g ⟨p.val - i, by omega⟩ ⟨q.val - i, by omega⟩ else 0)
  else (if p = q then 1 else 0)
def liftVec (k i r' : ℕ) (v : Fin (2 * r' + k + 1) → ℂ) : Fin (2 * (i + r') + k + 1) → ℂ := fun p =>
  if hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i then v ⟨p.val - i, by omega⟩ else 0
def LevHom : Prop :=
  ∀ k i r' : ℕ, ιLev k i r' 1 = 1 ∧
    ∀ g h : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ,
      ιLev k i r' (g * h) = ιLev k i r' g * ιLev k i r' h
def LevUH : Prop :=
  ∀ (k i r' : ℕ) (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ),
    g ∈ UH (Hpk k r') → ιLev k i r' g ∈ UH (Hpk k (i + r'))
def LevN : Prop :=
  ∀ (k i r' : ℕ) (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ),
    g ∈ Nset k r' → ιLev k i r' g ∈ Nset k (i + r')
def LevUW : Prop :=
  ∀ (k i r' : ℕ) (z : Fin (2 * r' + k + 1) → ℂ) (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ),
    g ∈ UWset k r' z → ιLev k i r' g ∈ UWset k (i + r') (liftVec k i r' z)
def LevWb : Prop :=
  ∀ (k i r' : ℕ) (z : Fin (2 * r' + k + 1) → ℂ), inWb k r' z →
    inWb k (i + r') (liftVec k i r' z) ∧ Tz k (i + r') (liftVec k i r' z) = Tz k r' z
def LevEll : Prop :=
  ∀ (k i r' : ℕ) (z : Fin (2 * r' + k + 1) → ℂ) (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ),
    ell k (i + r') (liftVec k i r' z) (ιLev k i r' g) = ell k r' z g
variable {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
def EqF (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp))
    (π' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wq)) :
    Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wp)) :=
  {J | SmoothOnH (Hpk k r) J ∧
    (∀ g ∈ UH (Hpk k r), ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r,
      J (n * g * n') = (psi k r z c n * psi k r z' c n') • J g) ∧
    (∀ g ∈ UH (Hpk k r), ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z',
      J (h * g * h') = (π h).comp ((J g).comp (π' h')))}
def KKeps (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (ε : ℝ) :
    Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wp)) :=
  {J | ∀ g, J g ≠ 0 → ε ≤ Gf k r z z' g}
def KKGGeps (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (ε : ℝ) :
    Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wp)) :=
  {J | ∀ g, J g ≠ 0 → ε ≤ GGf k r z z' g}
def cOf {r : ℕ} (x : Fin (r + 1) → ℂ) : Fin r → ℂ := fun a => x a.castSucc
def zOf {r : ℕ} (x : Fin (r + 1) → ℂ) : ℂ := x (Fin.last r)
def wbPart (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Fin (k + 1) → ℂ := fun j => v (wI k r j)
def IsSection (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    Prop :=
  (∀ i j : Fin (k + 1), ContDiffOn ℝ ∞ (fun ζ => μsec ζ i j) {ζ : ℂ | Tz k r z * Tz k r z' < Complex.normSq ζ}) ∧
  ∀ ζ : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ →
    Matrix.conjTranspose (μsec ζ) * Hb k * μsec ζ = Hb k ∧ herm (Hb k) (μsec ζ *ᵥ wbPart k r z') (wbPart k r z) = ζ
def BDom (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (Fin (r + 1) → ℂ) :=
  {x | x ∈ OmX (r + 1) ∧ Tz k r z * Tz k r z' < Complex.normSq (zOf x)}
open Classical in

def Btr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → E) :
    (Fin (r + 1) → ℂ) → E := fun x =>
  if x ∈ BDom k r z z' then
    ((((∏ a : Fin r, ‖cOf x a‖ ^ (Mdim k r a - 1)) *
        (Complex.normSq (zOf x) - Tz k r z * Tz k r z') ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) •
      J (bigCell k r (cOf x) (μsec (zOf x))))
  else 0
def LocalOn {m : ℕ} {E : Type*} (D : Set (Fin m → ℂ)) (R : ((Fin m → ℂ) → E) → (Fin m → ℂ) → E) : Prop :=
  ∀ φ ψ : (Fin m → ℂ) → E, (∀ x ∈ D, φ x = ψ x) → ∀ x ∈ D, R φ x = R ψ x
def HasRadialPart (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp))
    (π' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wq))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (K : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wp)))
    (Θ : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wp)) →
      Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wp))
    (R : ((Fin (r + 1) → ℂ) → (Wq →L[ℂ] Wp)) → (Fin (r + 1) → ℂ) → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ J ∈ EqF k r z z' c π π' ∩ K, ∀ x ∈ BDom k r z z', Btr k r z z' μsec (Θ J) x = R (Btr k r z z' μsec J) x
def BtrLin : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (J₁ J₂ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → E) (a : ℂ),
    Btr k r z z' μsec (J₁ + J₂) = Btr k r z z' μsec J₁ + Btr k r z z' μsec J₂ ∧
    Btr k r z z' μsec (a • J₁) = a • Btr k r z z' μsec J₁
def EqFSub : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp))
    (π' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wq)) (ε : ℝ),
    (0 ∈ EqF k r z z' c π π' ∧
      (∀ J₁ ∈ EqF k r z z' c π π', ∀ J₂ ∈ EqF k r z z' c π π', J₁ + J₂ ∈ EqF k r z z' c π π') ∧
      (∀ (a : ℂ), ∀ J ∈ EqF k r z z' c π π', a • J ∈ EqF k r z z' c π π')) ∧
    (0 ∈ KKeps (Wp := Wp) (Wq := Wq) k r z z' ε ∧
      (∀ J₁ ∈ KKeps (Wp := Wp) (Wq := Wq) k r z z' ε, ∀ J₂ ∈ KKeps (Wp := Wp) (Wq := Wq) k r z z' ε,
        J₁ + J₂ ∈ KKeps (Wp := Wp) (Wq := Wq) k r z z' ε) ∧
      (∀ (a : ℂ), ∀ J ∈ KKeps (Wp := Wp) (Wq := Wq) k r z z' ε, a • J ∈ KKeps (Wp := Wp) (Wq := Wq) k r z z' ε))
def RadAdd : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp))
    (π' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wq))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (K : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wp)))
    (Θ₁ Θ₂ : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wp)) →
      Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wp))
    (R₁ R₂ : ((Fin (r + 1) → ℂ) → (Wq →L[ℂ] Wp)) → (Fin (r + 1) → ℂ) → (Wq →L[ℂ] Wp)),
    HasRadialPart k r z z' c π π' μsec K Θ₁ R₁ → HasRadialPart k r z z' c π π' μsec K Θ₂ R₂ →
      HasRadialPart k r z z' c π π' μsec K (fun J => Θ₁ J + Θ₂ J) (fun φ => R₁ φ + R₂ φ)
def RadSmul : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp))
    (π' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wq))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (K : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wp)))
    (Θ : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wp)) →
      Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wp))
    (R : ((Fin (r + 1) → ℂ) → (Wq →L[ℂ] Wp)) → (Fin (r + 1) → ℂ) → (Wq →L[ℂ] Wp)) (a : ℂ),
    HasRadialPart k r z z' c π π' μsec K Θ R →
      HasRadialPart k r z z' c π π' μsec K (fun J => a • Θ J) (fun φ => a • R φ)
def RadComp : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp))
    (π' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wq))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (K : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wp)))
    (Θ₁ Θ₂ : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wp)) →
      Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wp))
    (R₁ R₂ : ((Fin (r + 1) → ℂ) → (Wq →L[ℂ] Wp)) → (Fin (r + 1) → ℂ) → (Wq →L[ℂ] Wp)),
    HasRadialPart k r z z' c π π' μsec K Θ₁ R₁ → HasRadialPart k r z z' c π π' μsec K Θ₂ R₂ →
      (∀ J ∈ EqF k r z z' c π π' ∩ K, Θ₂ J ∈ EqF k r z z' c π π' ∩ K) → LocalOn (BDom k r z z') R₁ →
        HasRadialPart k r z z' c π π' μsec K (Θ₁ ∘ Θ₂) (R₁ ∘ R₂)
def BtrIsom : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → E),
    1 ≤ k →
      (∫⁻ x : Fin (r + 1) → ℂ, ENNReal.ofReal (‖Btr k r z z' μsec J x‖ ^ 2 *
          (∏ a : Fin r, Complex.normSq (cOf x a))⁻¹)) =
        jNormSq k r (Tz k r z) (Tz k r z') (fun p : (Fin r → ℂ) × ℂ => J (bigCell k r p.1 (μsec p.2)))
def SectionExists : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' →
    0 < Tz k r z → 0 < Tz k r z' → ∃ μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsSection k r z z' μsec
abbrev Op (m : ℕ) (E : Type*) := ((Fin m → ℂ) → E) → (Fin m → ℂ) → E
def opMatApply {m : ℕ} {E : Type*} [AddCommGroup E] (M : Matrix (Fin 2) (Fin 2) (Op m E))
    (φ : Fin 2 → (Fin m → ℂ) → E) : Fin 2 → (Fin m → ℂ) → E :=
  fun a => ∑ b : Fin 2, M a b (φ b)
def opMatMul {m : ℕ} {E : Type*} [AddCommGroup E] (M N : Matrix (Fin 2) (Fin 2) (Op m E)) :
    Matrix (Fin 2) (Fin 2) (Op m E) :=
  fun a b f => ∑ c : Fin 2, M a c (N c b f)
def liftOp {m : ℕ} {E : Type*} (R : Op m E) : Op (m + 1) E :=
  fun φ x => R (fun y => φ (Fin.cons (x 0) y)) (Fin.tail x)
def liftMat {m : ℕ} {E : Type*} (M : Matrix (Fin 2) (Fin 2) (Op m E)) : Matrix (Fin 2) (Fin 2) (Op (m + 1) E) :=
  fun a b => liftOp (M a b)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def Tmat {m : ℕ} (l : Fin m) (Y : ℂ) : Matrix (Fin 2) (Fin 2) (Op m E) :=
  Matrix.of ![![fun f => Y • f + pOp l f, fun f => -(cOp l f)], ![ciOp l, fun _ => 0]]
def TmatStar {m : ℕ} (l : Fin m) (Y : ℂ) : Matrix (Fin 2) (Fin 2) (Op m E) :=
  Matrix.of ![![fun f => Y • f - pbOp l f, cbiOp l], ![fun f => -(cbOp l f), fun _ => 0]]
def TmatV {m : ℕ} (l : Fin m) (Y : ℂ) : Matrix (Fin 2) (Fin 2) (Op m E) :=
  Matrix.of ![![fun f => Y • f - pbOp l f, fun f => -(cbOp l f)], ![cbiOp l, fun _ => 0]]
def qPoly {k : ℕ} (T T' : ℝ) (u u' : Fin k → ℝ) (Y : ℂ) : ℂ :=
  -((T * T' : ℝ) : ℂ) * ∏ i : Fin k, ((Y + 1 / 2 + (u i : ℂ)) * (Y + 1 / 2 + (u' i : ℂ)))
def xPoly {j : ℕ} (ρ : Fin j → ℝ) (Y : ℂ) : ℂ := ∏ l : Fin j, (Y + (ρ l : ℂ))
def IsCut {k : ℕ} (u u' : Fin k → ℝ) (I : Set ℝ) : Prop :=
  ∃ (l : Fin k) (a b : ℝ), u l ≠ u' l ∧ a ≤ b ∧ I = Set.Icc a b ∧
    min (-u l) (-u' l) < a ∧ b < max (-u l) (-u' l) ∧
    ∀ i : Fin k, ∀ y ∈ I, 2 ≤ |y + u i| ∧ 2 ≤ |y + u' i|
end Formalism.QuantumDeterminants


