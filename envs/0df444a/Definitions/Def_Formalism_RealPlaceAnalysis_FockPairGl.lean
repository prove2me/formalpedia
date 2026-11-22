-- Prove2me | Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
-- name    : Formalism_RealPlaceAnalysis_FockPairGl
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:48:11.555674+00:00
-- url     : https://prove2.me/theorems/8b8429e1-cecc-46d6-89f7-c9f1d207199d
-- title:
--   Fock Pair Gl
-- statement:
--   Definitions and structural lemmas for Fock Pair Gl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/FockPairGl.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.REAL
def fockF {σ : Type*} (f g : MvPolynomial σ ℂ) : ℂ :=
  ∑ m ∈ f.support, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ)
def sgnv {M n' : ℕ} (ε : Fin M → Bool) (ε' : Fin n' → Bool) (i : Fin M) (a : Fin n') : Bool :=
  ε i == ε' a
def bop {M n' : ℕ} (ε : Fin M → Bool) (ε' : Fin n' → Bool) (i : Fin M) (a : Fin n') :
    Module.End ℂ (MvPolynomial (Fin M × Fin n') ℂ) :=
  if sgnv ε ε' i a then (pderiv (i, a)).toLinearMap
  else LinearMap.mulLeft ℂ (X (i, a))
def bpl {M n' : ℕ} (ε : Fin M → Bool) (ε' : Fin n' → Bool) (i : Fin M) (a : Fin n') :
    Module.End ℂ (MvPolynomial (Fin M × Fin n') ℂ) :=
  if sgnv ε ε' i a then LinearMap.mulLeft ℂ (X (i, a))
  else -(pderiv (i, a)).toLinearMap
def Eg {M n' : ℕ} (ε : Fin M → Bool) (ε' : Fin n' → Bool) (i j : Fin M) :
    Module.End ℂ (MvPolynomial (Fin M × Fin n') ℂ) :=
  ∑ a, bpl ε ε' i a * bop ε ε' j a
def Eg' {M n' : ℕ} (ε : Fin M → Bool) (ε' : Fin n' → Bool) (a b : Fin n') :
    Module.End ℂ (MvPolynomial (Fin M × Fin n') ℂ) :=
  -∑ i, bpl ε ε' i b * bop ε ε' i a
def NN {M n' : ℕ} (ε : Fin M → Bool) (ε' : Fin n' → Bool) :
    Module.End ℂ (MvPolynomial (Fin M × Fin n') ℂ) :=
  ∑ i, Eg ε ε' i i
def CCR : Prop :=
  ∀ (M n' : ℕ) (ε : Fin M → Bool) (ε' : Fin n' → Bool) (i j : Fin M) (a b : Fin n'),
    bop ε ε' i a * bpl ε ε' j b - bpl ε ε' j b * bop ε ε' i a = (if i = j ∧ a = b then 1 else 0) ∧
    bop ε ε' i a * bop ε ε' j b = bop ε ε' j b * bop ε ε' i a ∧
    bpl ε ε' i a * bpl ε ε' j b = bpl ε ε' j b * bpl ε ε' i a
def FockPairGl : Prop :=
  ∀ (M n' : ℕ) (ε : Fin M → Bool) (ε' : Fin n' → Bool),
    GlRel (Eg ε ε') ∧ GlRel (Eg' ε ε') ∧
    ∀ (i j : Fin M) (a b : Fin n'), Eg ε ε' i j * Eg' ε ε' a b = Eg' ε ε' a b * Eg ε ε' i j
def FockAdj : Prop :=
  ∀ (M n' : ℕ) (ε : Fin M → Bool) (ε' : Fin n' → Bool) (f g : MvPolynomial (Fin M × Fin n') ℂ),
    (∀ (i : Fin M) (a : Fin n'), fockF (bop ε ε' i a f) g =
      (if sgnv ε ε' i a then 1 else -1) * fockF f (bpl ε ε' i a g)) ∧
    (∀ i j : Fin M, fockF (Eg ε ε' i j f) g = (sgn ε i j : ℂ) * fockF f (Eg ε ε' j i g)) ∧
    (∀ a b : Fin n', fockF (Eg' ε ε' a b f) g = (sgn ε' a b : ℂ) * fockF f (Eg' ε ε' b a g))
def FockCas : Prop :=
  ∀ (M n' : ℕ) (ε : Fin M → Bool) (ε' : Fin n' → Bool),
    NN ε ε' = -∑ a, Eg' ε ε' a a ∧
    Cas (Eg ε ε') - (M : ℂ) • NN ε ε' = Cas (Eg' ε ε') - (n' : ℂ) • NN ε ε'
end Formalism.REAL


