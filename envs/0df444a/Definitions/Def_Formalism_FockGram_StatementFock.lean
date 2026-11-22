-- Prove2me | Definitions.Def_Formalism_FockGram_StatementFock
-- name    : Formalism_FockGram_StatementFock
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:02:41.06265+00:00
-- url     : https://prove2.me/theorems/af074728-b9cf-40d7-860e-8ea790fd41d4
-- title:
--   Statement Fock
-- statement:
--   Definitions and structural lemmas for Statement Fock, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FockGram/StatementFock.lean

import Definitions.Def_Formalism_SmithDeterminants_StatementGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix MvPolynomial
noncomputable section
namespace Formalism.E
def fock {R τ : Type*} [CommRing R] [StarRing R] (f g : MvPolynomial τ R) : R :=
  ∑ m ∈ f.support, f.coeff m * star (g.coeff m) * (Formalism.A.mfact m : R)
def fockGram {R τ ι : Type*} [CommRing R] [StarRing R] (v : ι → MvPolynomial τ R) :
    Matrix ι ι R :=
  Matrix.of fun i j => fock (v i) (v j)
def symMono {R σ τ : Type*} [CommRing R] {a : ℕ} (e : σ → MvPolynomial τ R) (s : Sym σ a) :
    MvPolynomial τ R :=
  ((s : Multiset σ).map e).prod
def symFact {σ : Type*} [DecidableEq σ] {a : ℕ} (s : Sym σ a) : ℕ :=
  Formalism.A.mfact (Multiset.toFinsupp (s : Multiset σ))
def symPow {R σ : Type*} [CommRing R] [Fintype σ] [DecidableEq σ] (a : ℕ) (A : Matrix σ σ R) :
    Matrix (Sym σ a) (Sym σ a) R :=
  Matrix.of fun s t => coeff (Multiset.toFinsupp (t : Multiset σ))
    (((s : Multiset σ).map fun i => ∑ j, C (A i j) * X j).prod)
def symGram {R σ : Type*} [CommRing R] [Fintype σ] [DecidableEq σ] (a : ℕ)
    (G : Matrix σ σ R) : Matrix (Sym σ a) (Sym σ a) R :=
  symPow a G * Matrix.diagonal fun t => (symFact t : R)
def FockSesq : Prop :=
  ∀ (R τ : Type) [CommRing R] [StarRing R],
    ∃ B : MvPolynomial τ R →ₗ[R] MvPolynomial τ R →ₗ⋆[R] R, ∀ f g, B f g = fock f g
def FockHerm : Prop :=
  ∀ (R τ : Type) [CommRing R] [StarRing R] (f g : MvPolynomial τ R),
    star (fock f g) = fock g f
def FockBridge : Prop :=
  (∀ (τ : Type) (f g : MvPolynomial τ ℤ), Formalism.A.fockZ f g = fock f g) ∧
  (∀ (τ : Type) (f g : MvPolynomial τ GaussianInt), Formalism.A.fockG f g = fock f g)
def FockPerm : Prop :=
  ∀ (R τ : Type) [CommRing R] [StarRing R] (a : ℕ) (x y : Fin a → MvPolynomial τ R),
    (∀ s, (x s).IsHomogeneous 1) → (∀ t, (y t).IsHomogeneous 1) →
    fock (∏ s, x s) (∏ t, y t) = (Matrix.of fun s t => fock (x s) (y t)).permanent
def FockGramSym : Prop :=
  ∀ (R σ τ : Type) [CommRing R] [StarRing R] [Fintype σ] [DecidableEq σ] (a : ℕ)
    (e : σ → MvPolynomial τ R), (∀ i, (e i).IsHomogeneous 1) →
    fockGram (symMono (a := a) e) = symGram a (fockGram e)
def DetSymPow : Prop :=
  ∀ (R σ : Type) [CommRing R] [Fintype σ] [DecidableEq σ] (a : ℕ) (A : Matrix σ σ R),
    (symPow a A).det = A.det ^ (Fintype.card σ + a - 1).choose (Fintype.card σ)
def DetSymGram : Prop :=
  ∀ (R σ : Type) [CommRing R] [Fintype σ] [DecidableEq σ] (a : ℕ) (G : Matrix σ σ R),
    (symGram a G).det =
      G.det ^ (Fintype.card σ + a - 1).choose (Fintype.card σ) * ∏ t : Sym σ a, (symFact t : R)
def DetFockSym : Prop :=
  ∀ (R σ τ : Type) [CommRing R] [StarRing R] [Fintype σ] [DecidableEq σ] (a : ℕ)
    (e : σ → MvPolynomial τ R), (∀ i, (e i).IsHomogeneous 1) →
    (fockGram (symMono (a := a) e)).det =
      (fockGram e).det ^ (Fintype.card σ + a - 1).choose (Fintype.card σ) *
        ∏ t : Sym σ a, (symFact t : R)
def FockStd : Prop :=
  ∀ (R σ : Type) [CommRing R] [StarRing R] [Fintype σ] [DecidableEq σ] (a : ℕ),
    fockGram (symMono (a := a) (X : σ → MvPolynomial σ R)) =
      Matrix.diagonal (fun t => (symFact t : R)) ∧
    (fockGram (symMono (a := a) (X : σ → MvPolynomial σ R))).det =
      ∏ t : Sym σ a, (symFact t : R)
end Formalism.E


