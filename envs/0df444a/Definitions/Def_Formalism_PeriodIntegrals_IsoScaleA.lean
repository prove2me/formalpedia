-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_IsoScaleA
-- name    : Formalism_PeriodIntegrals_IsoScaleA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:38:46.426723+00:00
-- url     : https://prove2.me/theorems/658dc76a-4661-458e-97fd-5117673cdcfc
-- title:
--   Iso Scale A
-- statement:
--   Definitions and structural lemmas for Iso Scale A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/IsoScaleA.lean

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
namespace PI.IsoScaleA
def ColChoice {Lt : Type} (N1 : ℕ) (nu : Lt → YoungDiagram) : Type :=
  ∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N1
def minY {Lt k : Type} [Fintype Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (J : ColChoice N nu)
    (y : Lt → Fin N → ℕ → k) : k :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i j : Fin ((nu s).colLen c) => y s (J s c i) (j : ℕ))
def colsOf {k : Type} [Zero k] {N : ℕ} (Y : Matrix (Fin N) (Fin N) k) : Fin N → ℕ → k :=
  fun a j => if h : j < N then Y a ⟨j, h⟩ else 0
abbrev LaC {Lt : Type} (N : ℕ) (nu : Lt → YoungDiagram) : Type := ColChoice N nu → ℂ
def hvC {Lt : Type} [Fintype Lt] (N : ℕ) (nu : Lt → YoungDiagram) (x : Lt → Fin N → ℕ → ℂ) : LaC N nu :=
  fun J => minY N nu J x
def Vnu {Lt : Type} [Fintype Lt] (N : ℕ) (nu : Lt → YoungDiagram) : Submodule ℂ (LaC N nu) :=
  Submodule.span ℂ (Set.range (hvC N nu))
def l2 {Lt : Type} {N : ℕ} {nu : Lt → YoungDiagram} (φ : LaC N nu) : ℝ := ∑ᶠ J, ‖φ J‖ ^ 2
def prC {Lt : Type} {N : ℕ} {nu : Lt → YoungDiagram} (φ ψ : LaC N nu) : ℂ := ∑ᶠ J, φ J * ψ J
def VnuMap {Lt : Type} [Fintype Lt] {N N' : ℕ} (nu : Lt → YoungDiagram) (f : Lt → Matrix (Fin N') (Fin N) ℂ)
    (φ : LaC N nu) : LaC N' nu :=
  fun I => ∑ᶠ J : ColChoice N nu, (∏ s, ∏ c : Fin ((nu s).rowLen 0),
    Matrix.det (Matrix.of fun i k : Fin ((nu s).colLen c) => f s (I s c i) (J s c k))) * φ J
def canC {Lt : Type} [Fintype Lt] {N : ℕ} {nu : Lt → YoungDiagram} (φ : LaC N nu) (y : Lt → Fin N → ℕ → ℂ) : ℂ :=
  prC φ (hvC N nu y)
abbrev Idx (T : Type) (N N' : ℕ) : Type := T × Fin N' × Fin N
abbrev FrV (T : Type) (N : ℕ) : Type := T × Fin N × Fin N
abbrev VC (T : Type) (N N' : ℕ) : Type := T → Fin N' → Fin N → ℂ
abbrev Mono (T : Type) (N N' : ℕ) : Type := (T × Fin N' × Fin N) →₀ ℕ
open Classical in

def coordV {T : Type} {N N' : ℕ} (k : T × Fin N' × Fin N) : VC T N N' :=
  fun τ i j => if τ = k.1 ∧ i = k.2.1 ∧ j = k.2.2 then 1 else 0
def taylor {T : Type} [Fintype T] {N N' : ℕ} (G : VC T N N' → ℂ) (α : Mono T N N') : ℂ :=
  iteratedFDeriv ℂ (Multiset.card α.toMultiset) G 0
      (fun i => coordV (α.toMultiset.toList.get ⟨i, by simpa using i.2⟩)) /
    (α.prod fun _ n => (n.factorial : ℂ))
def applyAt0 {T : Type} [Fintype T] {N N' : ℕ} (P : MvPolynomial (Idx T N N') ℂ) (G : VC T N N' → ℂ) : ℂ :=
  ∑ α ∈ P.support, MvPolynomial.coeff α P * (α.prod fun _ n => (n.factorial : ℂ)) * taylor G α
def evFr {T : Type} {N : ℕ} (Q : MvPolynomial (FrV T N) ℂ) (y : T → Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  MvPolynomial.eval (fun k : FrV T N => y k.1 k.2.1 k.2.2) Q
def polD {T : Type} {N N' : ℕ} (s : T → ℂ) (Q : MvPolynomial (FrV T N) ℂ)
    (y' : T → Matrix (Fin N') (Fin N') ℂ) : MvPolynomial (Idx T N N') ℂ :=
  MvPolynomial.aeval (fun k : FrV T N => ∑ b : Fin N',
    MvPolynomial.C (s k.1 * (if h : (k.2.2 : ℕ) < N' then y' k.1 b ⟨k.2.2, h⟩ else 0)) *
      MvPolynomial.X ((k.1, b, k.2.1) : Idx T N N')) Q
def PIJ {Lt T : Type} [Fintype Lt] (tp : Lt → T) {N N' : ℕ} (nu : Lt → YoungDiagram) (s : T → ℂ) (I : ColChoice N' nu)
    (J : ColChoice N nu) : MvPolynomial (Idx T N N') ℂ :=
  ∏ z, ∏ c : Fin ((nu z).rowLen 0), Matrix.det (Matrix.of fun i k : Fin ((nu z).colLen c) =>
    MvPolynomial.C (s (tp z)) * MvPolynomial.X ((tp z, I z c i, J z c k) : Idx T N N'))
def AOp {Lt T : Type} [Fintype Lt] [Fintype T] (tp : Lt → T) {N N' : ℕ} (nu : Lt → YoungDiagram) (s : T → ℂ) (Θ : VC T N N' → ℂ)
    (φ : LaC N nu) : LaC N' nu :=
  fun I => ∑ᶠ J : ColChoice N nu, applyAt0 (PIJ tp nu s I J) Θ * φ J
abbrev frC {Lt T : Type} (tp : Lt → T) {N : ℕ} (y : T → Matrix (Fin N) (Fin N) ℂ) : Lt → Fin N → ℕ → ℂ :=
  fun z => colsOf (y (tp z))
def IsoScaleA : Prop :=
  ∀ (Lt T : Type) [Fintype Lt] [DecidableEq Lt] [Fintype T] (tp : Lt → T) (N N' : ℕ) (nu : Lt → YoungDiagram) (c s : T → ℂ) (Θ : VC T N N' → ℂ) (φ : LaC N nu),
    AOp tp nu (fun τ => c τ * s τ) Θ φ = (∏ z : Lt, c (tp z) ^ (nu z).card) • AOp tp nu s Θ φ
end PI.IsoScaleA


