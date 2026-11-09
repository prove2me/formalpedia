-- Prove2me | Definitions.Def_WitnessIsolation_AffineCollapse_regions
-- name    : WitnessIsolation_AffineCollapse_regions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:33:48.882256+00:00
-- url     : https://prove2.me/theorems/0afe7ac1-7345-436b-8dbb-72aaeff4d09a
-- title:
--   Product regions, SAT-query outputs, and Boolean flags
-- statement:
--   For t blocks of width v, a pair of known points pᵢ,qᵢ represents the nonempty set {pᵢ,qᵢ}; equal points represent a singleton. The region K is their Cartesian product. RegionSingleton(D,p,q) asserts exactly one satisfying point of D in K:
--
--   $$|\operatorname{Sol}(D)\cap K|=1.$$
--
--   The region-input encoding concatenates a padded circuit description and the two explicit points in every block. A query-producing multi-output circuit returns 2t+1 padded descriptions, each extracted from its own output segment. The acceptance formula on the SAT answer bits is: the first answer is true, and in every pair of remaining answers at least one is false.
--
--   For z uniform in the t-dimensional cube, the j-th flag fixes coordinates with zero-based indices at least j to their values in z. Thus F₀={z} and F_t is the full cube. These definitions make the region-test resource claim and the strict flag bound independent of the proof constructions.
--
--   **Formalization Note** The product uses row-major block order. Repeated listed points are permitted; no distinctness hypothesis is introduced. Empty products (t=0) and zero-width blocks (v=0) remain meaningful.
-- source:
--   Sebastian ben daniel, STOC 2027 submission #346 (October 2026), §5, printed p. 10, PDF p. 11, Lemmas 5.1–5.2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/346.pdf; PDF SHA256 969057d4c1837a5ebf1d45c70a14c1d66f0d76610c6233f151e2402e7611f42e

import Definitions.Def_WitnessIsolation_AffineCollapse_probability

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace WitnessIsolation.AffineCollapse

/-- Lists of one or two points are represented by a pair; repetition means a singleton. -/
def InRegion {t v : ℕ} (p q : Fin t → Bits v) (x : Bits (t*v)) : Prop :=
  ∀ i : Fin t, (∀ k : Fin v, x (finProdFinEquiv (i,k)) = p i k) ∨
    (∀ k : Fin v, x (finProdFinEquiv (i,k)) = q i k)

def RegionSingleton {t v : ℕ} (D : Description) (p q : Fin t → Bits v) : Prop :=
  ∃! x : Bits (t*v), InRegion p q x ∧ D.eval (word (List.ofFn x) D.inputs) = true

def regionInputWidth (s v t : ℕ) : ℕ := paddedWidth s + 2*t*v

def regionInput {s v t : ℕ} (h : Bits (paddedWidth s)) (p q : Fin t → Bits v) :
    Bits (regionInputWidth s v t) :=
  word (List.ofFn h ++ (List.ofFn (fun i : Fin t => List.ofFn (p i) ++ List.ofFn (q i))).flatten)
    (regionInputWidth s v t)

def queryOutput {n t b : ℕ} (C : Circuit n ((2*t+1)*paddedWidth b)) (x : Bits n)
    (j : Fin (2*t+1)) : Bits (paddedWidth b) :=
  fun k => C.eval x (finProdFinEquiv (j,k))

def answersAccept {t : ℕ} (a : Bits (2*t+1)) : Prop :=
  a ⟨0,by omega⟩ = true ∧ ∀ i : Fin t,
    a ⟨2*i.val+1,by omega⟩ = false ∨ a ⟨2*i.val+2,by omega⟩ = false

/-- Fin t uses indices 0,...,t-1: the paper's coordinates i>j are the indices i≥j. -/
def flag {t : ℕ} (z : Bits t) (j : ℕ) : Finset (Bits t) :=
  Finset.univ.filter (fun x => ∀ i : Fin t, j ≤ i.val → x i = z i)

end WitnessIsolation.AffineCollapse


