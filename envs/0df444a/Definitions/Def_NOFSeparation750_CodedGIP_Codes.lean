-- Prove2me | Definitions.Def_NOFSeparation750_CodedGIP_Codes
-- name    : NOFSeparation750_CodedGIP_Codes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T02:41:17.657902+00:00
-- url     : https://prove2.me/theorems/743edd08-11f6-492b-aea3-b0747d3b5deb
-- title:
--   Linear product codes, compatibility, bases, and information sets
-- statement:
--   A linear code is a linear subspace $V\le\mathbb F_q^r$. Weight counts nonzero coordinates. For nonzero $V$, its distance is the smallest weight of a nonzero word. Its $k$-product is
--   $$V^{\odot k}=\operatorname{span}_{\mathbb F_q}\{a_1\odot\cdots\odot a_k:a_i\in V\}.$$
--   For $k,r\ge1$ and $\varepsilon,\delta\in(0,1]$, compatibility means exactly product containment, dimension at least $\varepsilon r$, and distance at least $\delta r$. The distance-bearing code is explicitly nonzero. Its zero-code default distance is zero and cannot satisfy the nonzero-code convention in compatibility. Compatibility includes no nesting or computational assumption.
--
--   A code presentation supplies an ordered basis, whose rows form its generator matrix. Encoding is the actual linear combination of those basis vectors. An information set supplies distinct coordinates of cardinality $\dim V$ together with the linear restriction bijection; its recovery map is precisely the inverse of restriction. These objects connect coefficient and coordinate representations without introducing independent encoders.
-- source:
--   Haoyu Wang, Yimeng Wang, Pei Wu, STOC 2027 submission #750 (October 2026), §2, pp.5–6; Definition 3.1, p.7; canonical PDF SHA-256 b28ac89d573094bcafec49dc3a1eeadc9e95b5c3074c478d242f60a2818a42ce

import Mathlib

noncomputable section

namespace NOFSeparation750.CodedGIP
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev LinearCode (F : Type) [Field F] (r : ℕ) := Submodule F (Fin r → F)

def weight {F : Type} [Zero F] {r : ℕ} (x : Fin r → F) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ 0).card

/-- The minimum of the finite nonempty set of nonzero weights for a nonzero code.
At the zero code the totalized value is 0; compatibility excludes that case. -/
def distance {F : Type} [Field F] {r : ℕ} (V : LinearCode F r) : ℕ :=
  sInf {d | ∃ x ∈ V, x ≠ 0 ∧ weight x = d}

def productCode {F : Type} [Field F] {r : ℕ} (V : LinearCode F r) (k : ℕ) : LinearCode F r :=
  Submodule.span F {x | ∃ a : Fin k → V, x = fun t => ∏ i, (a i).val t}

/-- Definition 3.1. Nonzero W and positive length make the printed distance
well-defined; no nesting, basis, or algorithm is part of compatibility. -/
def Compatible {F : Type} [Field F] {r : ℕ} (V W : LinearCode F r)
    (k : ℕ) (ε δ : ℝ) : Prop :=
  1 ≤ k ∧ 1 ≤ r ∧ 0 < ε ∧ ε ≤ 1 ∧ 0 < δ ∧ δ ≤ 1 ∧ W ≠ ⊥ ∧
  productCode V k ≤ W ∧ ε * r ≤ Module.finrank F V ∧ δ * r ≤ distance W

/-- Ordered basis; its rows are the generator matrix, not an unrelated encoder. -/
structure CodePresentation (F : Type) [Field F] (r : ℕ) where
  code : LinearCode F r
  dimension : ℕ
  basis : Module.Basis (Fin dimension) F code

def CodePresentation.encode {F : Type} [Field F] {r : ℕ}
    (P : CodePresentation F r) (u : Fin P.dimension → F) : P.code :=
  ∑ i, u i • P.basis i

structure CodePair (F : Type) [Field F] (r : ℕ) where
  small : CodePresentation F r
  large : CodePresentation F r

/-- An ordered information set with the genuine inverse of restriction. The
linear equivalence provides both inverse identities. -/
structure InformationSet {F : Type} [Field F] {r : ℕ} (V : LinearCode F r) where
  size : ℕ
  dimension_eq : size = Module.finrank F V
  coordinate : Fin size ↪ Fin r
  restriction : V ≃ₗ[F] (Fin size → F)
  restrict_eq : ∀ a t, restriction a t = a.val (coordinate t)

def InformationSet.recover {F : Type} [Field F] {r : ℕ} {V : LinearCode F r}
    (S : InformationSet V) : (Fin S.size → F) → V := S.restriction.symm

end NOFSeparation750.CodedGIP


