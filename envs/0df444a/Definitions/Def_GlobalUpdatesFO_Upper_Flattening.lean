-- Prove2me | Definitions.Def_GlobalUpdatesFO_Upper_Flattening
-- name    : GlobalUpdatesFO_Upper_Flattening
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:20:30.864577+00:00
-- url     : https://prove2.me/theorems/a3ecd605-3bd4-420b-9889-2b00fd4fc7e7
-- title:
--   The flattened signature Σ^K and the K-flattening A^K
-- statement:
--   Let $A$ be a $\Sigma$-structure and $K \subseteq U(A)$ a finite set of $m$ elements, enumerated as $\kappa_0, \dots, \kappa_{m-1}$. The **flattened signature** $\Sigma^K$ has, for each relation $R \in \Sigma$ and each partial function $\pi : \{0,\dots,\mathrm{arity}(R)-1\} \rightharpoonup K$, a relation $R^\pi$ of arity
--   $$\mathrm{arity}(R^\pi) = \mathrm{arity}(R) - |\mathrm{dom}(\pi)| .$$
--   The **$K$-flattening** $A^K$ is the $\Sigma^K$-structure on $U(A) \setminus K$ in which $\bar a \in R^\pi(A^K)$ iff $\bar a^\pi \in R(A)$, where $\bar a^\pi$ places $\pi(i)$ at each index $i \in \mathrm{dom}(\pi)$ and fills the other indices with the entries of $\bar a$ in consecutive order. The relation $R^\pi$ *names* the elements of the image of $\pi$. $\mathrm{maxarity}(\Sigma^K) = \mathrm{maxarity}(\Sigma)$.
--
--   $A^K$ records, on the remaining elements, everything $A$ says about their interaction with $K$; it is the operation through which robust sets and decompositions are defined.
--
--   **Formalization Note** $\Sigma^K$ depends only on $m$: the symbols are listed relation by relation, and within the block of $R$ the symbol $R^\pi$ is the $j$-th one, $0 \le j < (m+1)^{\mathrm{arity}(R)}$, where the $i$-th base-$(m+1)$ digit of $j$ is $0$ when $i \notin \mathrm{dom}(\pi)$ and $c + 1$ when $\pi(i) = \kappa_c$. For a `Finset` $K$ the enumeration is a fixed bijection with $\{0,\dots,|K|-1\}$; another enumeration only renames relation symbols.
-- source:
--   Korhonen, Sokołowski, On efficient global updates in first-order logic, STOC 2027 submission (manuscript sha256 ffb1e749…), p. 22, §3.7

import Mathlib
import Definitions.Def_GlobalUpdatesFO_Upper_Structure

set_option autoImplicit false

namespace GlobalUpdatesFO.Upper

/-- The `i`-th digit of `j` in base `m + 1`. A number `j < (m+1)^a` encodes the partial function
`π : [a] ⇀ [m]` with `π(i)` undefined when the digit is `0` and `π(i) = c` when the digit is
`c + 1`. -/
def piDigit (m j i : ℕ) : ℕ := (j / (m + 1) ^ i) % (m + 1)

/-- `|dom π|` for the partial function `π : [a] ⇀ [m]` encoded by `j`. -/
def numNamed (m a j : ℕ) : ℕ := ((List.range a).filter (fun i => piDigit m j i != 0)).length

/-- The **flattened signature** `Σ^K` for a named set `K = {κ_0, …, κ_{m−1}}` of `m` elements
(Korhonen, Sokołowski, *On efficient global updates in first-order logic*, STOC 2027 submission,
§3.7, p. 22): for each relation `R ∈ Σ` and each partial function `π : [arity(R)] ⇀ K` a relation
`R^π` of arity `arity(R) − |dom(π)|`. The symbols are listed relation by relation; within the block
of `R`, the symbol `R^π` sits at position `j < (m+1)^{arity(R)}`, where `j` encodes `π` digitwise
(`piDigit`).

**Formalization Note** `Σ^K` depends on `K` only through its size `m` and an enumeration of `K`: the
symbol `R^π` names the element `κ_c` by its index `c`. -/
def flatSig (σ : Signature) (m : ℕ) : Signature :=
  (List.finRange σ.length).flatMap (fun R =>
    (List.range ((m + 1) ^ (σ.get R))).map (fun j => σ.get R - numNamed m (σ.get R) j))

/-- The position of the first symbol of the block of `R` in `flatSig σ m`. -/
def flatOffset (σ : Signature) (m R : ℕ) : ℕ :=
  ((List.range R).map (fun R' => (m + 1) ^ (σ.getD R' 0))).sum

/-- The **`K`-flattening** `A^K` (§3.7, p. 22) for `K` enumerated (injectively) as
`κ_0, …, κ_{m−1}`: the `Σ^K`-structure on `U(A) \ K` with `ā ∈ R^π(A^K)` iff `ā^π ∈ R(A)`, where
`ā^π` places `π(i)` at every index `i ∈ dom(π)` and fills the other indices with the entries of `ā`
in consecutive order. -/
def flatten {σ : Signature} {U : Type*} {m : ℕ} (A : Structure σ U) (κ : Fin m → U) :
    Structure (flatSig σ m) {u : U // u ∉ Set.range κ} where
  rel p := {t | ∃ (R : Fin σ.length) (j : ℕ), j < (m + 1) ^ (σ.get R) ∧
      p.val = flatOffset σ m R + j ∧
      ∃ s ∈ A.rel R,
        (∀ (i : Fin (σ.get R)) (c : Fin m), piDigit m j i.val = c.val + 1 → s i = κ c) ∧
        ((List.finRange (σ.get R)).filter (fun i : Fin (σ.get R) => piDigit m j i.val == 0)).map s =
          List.ofFn (fun i => (t i).val)}

/-- An enumeration of a finite set `K` (a fixed bijection `Fin |K| ≃ K`). -/
noncomputable def enumOf {U : Type*} (K : Finset U) : Fin K.card → U :=
  fun i => (K.equivFin.symm i).val

/-- The flattening `A^K` at a finite subset `K ⊆ U(A)`, with `K` named through `enumOf K`.

**Formalization Note** Another enumeration of `K` renames the relation symbols of `Σ^K` and changes
no statement of the mission (types, nobles, robustness and components are invariant under renaming
relation symbols). -/
noncomputable def flattenAt {σ : Signature} {U : Type*} (A : Structure σ U) (K : Finset U) :
    Structure (flatSig σ K.card) {u : U // u ∉ Set.range (enumOf K)} :=
  flatten A (enumOf K)

end GlobalUpdatesFO.Upper


