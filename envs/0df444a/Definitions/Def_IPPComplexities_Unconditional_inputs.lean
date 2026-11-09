-- Prove2me | Definitions.Def_IPPComplexities_Unconditional_inputs
-- name    : IPPComplexities_Unconditional_inputs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:23:31.552312+00:00
-- url     : https://prove2.me/theorems/33a95eb7-a883-49f4-839b-0c5b8153c17f
-- title:
--   Boolean input slices and normalized Hamming proximity
-- statement:
--   A property $L$ is a set of finite Boolean lists. A length-$n$ input $x$ is a function from $\{0,\ldots,n-1\}$ to $\{0,1\}$; its ordered list belongs to $L$ exactly when $x$ lies in the length-$n$ slice. For two such inputs, define
--
--   $$d(x,y)=\frac{|\{i:x_i\ne y_i\}|}{n},\qquad
--   \operatorname{Far}(L,\varepsilon,x)\iff
--   \forall y\in L_n,\ d(x,y)>\varepsilon.$$
--
--   The zero-length distance is defined as zero. Every input is far from an empty slice, while a member is never far at positive proximity. These shared definitions supply the same input and distance conventions to both results, without an infimum of an empty real set.
-- source:
--   Noga Amit, Oded Goldreich, STOC 2027 submission #297 (October 2026), pp. 5–6, Definition 2.1 and its distance convention (PDF pp. 7–8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/297.pdf

import Mathlib

namespace IPPComplexities.Unconditional

/-- Boolean strings of exactly length n, with positions numbered from zero. -/
abbrev Input (n : ℕ) := Fin n → Bool

abbrev Property := Set (List Bool)

/-- The input presented to a full-input decision machine. -/
def inputList {n : ℕ} (x : Input n) : List Bool := List.ofFn x

/-- Normalized Hamming distance; the unique zero-length pair has distance zero. -/
noncomputable def hamming {n : ℕ} (x y : Input n) : ℝ :=
  ((Finset.univ.filter (fun i => x i ≠ y i)).card : ℝ) / n

/-- Universal comparison avoids giving an empty slice an artificial real infimum. -/
def Far (L : Property) {n : ℕ} (ε : ℝ) (x : Input n) : Prop :=
  ∀ y : Input n, inputList y ∈ L → ε < hamming x y

end IPPComplexities.Unconditional


