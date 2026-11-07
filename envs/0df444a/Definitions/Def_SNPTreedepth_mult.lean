-- Prove2me | Definitions.Def_SNPTreedepth_mult
-- name    : SNPTreedepth_mult
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:27:48.06581+00:00
-- url     : https://prove2.me/theorems/9c6639f4-ff03-4ae6-a7a6-61f946f81a48
-- title:
--   The $s$-multiplicity structure $R^s$, its tree $T^s$, $\mathrm{orig}$ and retained elements
-- statement:
--   Let $s\ge p\ge1$ and let $T$ be a treedepth decomposition of $R$. The **$s$-multiplicity structure** $R^s$ for $(R,T,p)$ with its tree $T^s$ is obtained as follows: keep the elements all of whose $p$-route entries $(t,i)$ have $i\le s$; then, processing bottom-up, give every vertex $w$ exactly $s$ children of each type $t$ that is $p$-abundant in $p\text{-type}(w)$ by attaching copies of the subtree of its smallest child of type $t$, copying every relation tuple along (all $p$-types are those of $(R,T)$). Fresh elements are ordered after the elements of $R$. Each element $y$ of $R^s$ has an **original** $\mathrm{orig}(y)\in V(R)$, and $y$ is **retained** if it is an element of $R$. For $s=p$ no copies are made and $R^p$ is an induced substructure of $R$.
--
--   $R^p$ is the bounded-size structure on which Algorithm A searches for a $p$-pure solution.
--
--   **Formalization Note** Elements of $R^s$ are named by addresses: the root is $[(p\text{-type}(\text{root}),1)]$, and below a vertex with original $x$ the children of type $t$ are $a\diamond(t,i)$ for $i=1,\dots,s$ if $t$ is $p$-abundant in $p\text{-type}(x)$ and for $i=1,\dots,n_t(x)$ otherwise; an index $i\le n_t(x)$ is the $i$-th real child, a larger one a copy of the smallest. The parent of an address drops its last entry. A tuple lies in $E_i^s$ iff its entries are pairwise ancestor-related in $T^s$ and their originals form a tuple of $E_i$. This reproduces Definition 26's procedure, with copies named by position; retained elements are the addresses that are $p$-routes in $T$ of their originals. Fresh elements are ordered by original and then by address code (the paper leaves their order arbitrary).
-- source:
--   Depian, Ganian, Greilhuber, Gründel, Wietheger, A Uniform Algorithm for Strict NP on Bounded-Treedepth Structures, STOC 2027 submission (manuscript sha256 98e4e1a9…), Definitions 26 and 27, pp.24–25 (PDF pp.25–26)

import Mathlib
import Definitions.Def_SNPTreedepth_Structure
import Definitions.Def_SNPTreedepth_treedepth
import Definitions.Def_SNPTreedepth_ptype

set_option autoImplicit false

namespace SNPTreedepth

section Mult

variable {σ : Signature} {V : Type*} [Fintype V] [LinearOrder V]

/-- The root of a rooted tree (`none` if there is no root). -/
noncomputable def RootedForest.root (T : RootedForest V) : Option V :=
  open Classical in if h : ∃ v, T.parent v = none then some h.choose else none

/-- The child of `x` that an address entry `(t, i)` points to in the construction of the
`s`-multiplicity structure: the `i`-th smallest child of `x` of vertex `p`-type `t` (in the total
order of `V`) when `x` has at least `i` such children, and otherwise (a copy) the smallest one,
whose subtree is the one copied in Definition 26 (p.24). -/
noncomputable def multChild (R : Structure σ V) (T : RootedForest V) (p : ℕ) (x : V) (t i : ℕ) :
    Option V :=
  open Classical in
  let L := ((T.children x).filter (fun c => ptype R T p c = t)).sort (· ≤ ·)
  if i ≤ L.length then L[i - 1]? else L[0]?

/-- The number of children of type `t` below a vertex of `T^s` whose original is `x`
(Depian et al., Definition 26 and Lemma 28 (4), pp.24–25): `s` when `t` is `p`-abundant in
`p-type(x)` (that is, `x` has at least `p` children of type `t`), and otherwise the number of
children of `x` of type `t`. -/
noncomputable def multBound (R : Structure σ V) (T : RootedForest V) (p s : ℕ) (x : V) (t : ℕ) : ℕ :=
  if p ≤ typeCount R T p x t then s else typeCount R T p x t

/-- The vertices of `T^s` at depth `d`, each as a pair (address, original). The address of a vertex
is the list of entries `(t, i)` along its root path; the original is `orig(y)` of Definition 27. -/
noncomputable def multLevel (R : Structure σ V) (T : RootedForest V) (p s : ℕ) :
    ℕ → Finset (List (ℕ × ℕ) × V)
  | 0 => ∅
  | 1 =>
    match T.root with
    | none => ∅
    | some r => {([(ptype R T p r, 1)], r)}
  | d + 2 =>
    open Classical in
    (multLevel R T p s (d + 1)).biUnion (fun q =>
      ((T.children q.2).image (ptype R T p)).biUnion (fun t =>
        (Finset.Icc 1 (multBound R T p s q.2 t)).biUnion (fun i =>
          match multChild R T p q.2 t i with
          | none => ∅
          | some c => {(q.1 ++ [(t, i)], c)})))

/-- All (address, original) pairs of the `s`-multiplicity structure. -/
noncomputable def multPairs (R : Structure σ V) (T : RootedForest V) (p s : ℕ) :
    Finset (List (ℕ × ℕ) × V) :=
  (Finset.range (Fintype.card V + 1)).biUnion (multLevel R T p s)

/-- The addresses of the elements of the `s`-multiplicity structure. -/
noncomputable def multDom (R : Structure σ V) (T : RootedForest V) (p s : ℕ) :
    Finset (List (ℕ × ℕ)) :=
  open Classical in (multPairs R T p s).image Prod.fst

/-- The element set `V(R^s)` of the **`s`-multiplicity structure** `R^s` for `(R, T, p)`
(Depian et al., Definition 26, pp.24–25), each element named by its address.

**Formalization Note** (equivalence with the copy procedure of Definition 26.) Definition 26 keeps
the elements whose `p`-route has all indices `≤ s` and then, bottom-up, gives every vertex `w`
exactly `s` children of each type `t` that is `p`-abundant in `p-type(w)` by attaching
`s − c_t` disjoint copies of the (already processed) subtree of the smallest child of type `t`;
all `p`-types are those of `(R, T)`. Here a vertex of `T^s` is named by its address: the root is
`[(p-type(root), 1)]`, and below a vertex with original `x` the children of type `t` are
`a ⋄ (t, i)` for `i = 1, …, s` if `t` is `p`-abundant in `p-type(x)`, and `i = 1, …, n_t(x)`
otherwise. Index `i ≤ n_t(x)` names the `i`-th smallest real child of type `t` (its address is
then its `p`-route in `T`); a larger index names a copy of the smallest one. This is exactly the
tree the procedure produces, with each copy identified by its position; the levels are built for
depths `1, …, |V|`, which covers every depth. -/
def MultElem (R : Structure σ V) (T : RootedForest V) (p s : ℕ) : Type :=
  {a : List (ℕ × ℕ) // a ∈ multDom R T p s}

namespace MultElem

variable (R : Structure σ V) (T : RootedForest V) (p s : ℕ)

noncomputable instance : Fintype (MultElem R T p s) := by
  unfold MultElem; infer_instance

noncomputable instance : DecidableEq (MultElem R T p s) := by
  unfold MultElem; infer_instance

end MultElem

/-- `orig(y)` (Depian et al., Definition 27, p.25): the retained element of `R` that the element
`y` of `R^s` is a copy of; `orig(y) = y` for a retained `y`. -/
noncomputable def orig {R : Structure σ V} {T : RootedForest V} {p s : ℕ} (a : MultElem R T p s) : V :=
  (Finset.mem_image.mp a.2).choose.2

/-- An element of `R^s` is **retained** (Depian et al., Definition 27, p.25) if it is an element of
`R`: its address is the `p`-route in `T` of its original, i.e. it is not a copy. -/
def Retained {R : Structure σ V} {T : RootedForest V} {p s : ℕ} (a : MultElem R T p s) : Prop :=
  route R T p (orig a) = a.1

/-- The sort key that orders `V(R^s)`: retained elements first, in the order of `R`
(Definition 26, p.25: "each fresh element of `R^s` is sorted after all elements of `R`, for an
arbitrary order among the fresh elements"); fresh elements are then ordered by their original and
by the code of their address. -/
noncomputable def multKey {R : Structure σ V} {T : RootedForest V} {p s : ℕ} (a : MultElem R T p s) :
    Bool ×ₗ (V ×ₗ ℕ) :=
  open Classical in toLex (decide (¬ Retained a), toLex (orig a, Encodable.encode a.1))

theorem multKey_injective (R : Structure σ V) (T : RootedForest V) (p s : ℕ) :
    Function.Injective (multKey (R := R) (T := T) (p := p) (s := s)) := by
  intro a b h
  have h2 : Encodable.encode a.1 = Encodable.encode b.1 := by
    have := congrArg (fun x => (ofLex (ofLex x).2).2) h
    simpa [multKey] using this
  exact Subtype.ext (Encodable.encode_injective h2)

/-- The total order on `V(R^s)` (Definition 26, p.25). -/
noncomputable instance (R : Structure σ V) (T : RootedForest V) (p s : ℕ) :
    LinearOrder (MultElem R T p s) :=
  LinearOrder.lift' multKey (multKey_injective R T p s)

theorem multLevel_spec (R : Structure σ V) (T : RootedForest V) (p s : ℕ) :
    ∀ d, ∀ q ∈ multLevel R T p s d, q.1.length = d ∧
      (2 ≤ d → ∃ q' ∈ multLevel R T p s (d - 1), q'.1 = q.1.dropLast) := by
  intro d
  induction d with
  | zero => intro q hq; simp [multLevel] at hq
  | succ d ih =>
    intro q hq
    rcases d with _ | d
    · simp only [multLevel] at hq
      split at hq
      · simp at hq
      · simp only [Finset.mem_singleton] at hq
        subst hq; simp
    · simp only [multLevel, Finset.mem_biUnion] at hq
      obtain ⟨q0, hq0, t, -, i, -, hc⟩ := hq
      split at hc
      · simp at hc
      · simp only [Finset.mem_singleton] at hc
        subst hc
        refine ⟨?_, fun _ => ⟨q0, ?_, ?_⟩⟩
        · simp [(ih q0 hq0).1]
        · simpa using hq0
        · simp

theorem multDom_spec (R : Structure σ V) (T : RootedForest V) (p s : ℕ) (a : List (ℕ × ℕ))
    (ha : a ∈ multDom R T p s) :
    1 ≤ a.length ∧ (2 ≤ a.length → a.dropLast ∈ multDom R T p s) := by
  classical
  simp only [multDom, multPairs, Finset.mem_image, Finset.mem_biUnion, Finset.mem_range] at ha
  obtain ⟨q, ⟨d, hd, hq⟩, rfl⟩ := ha
  obtain ⟨hlen, hpre⟩ := multLevel_spec R T p s d q hq
  rcases d with _ | d
  · simp [multLevel] at hq
  refine ⟨by omega, fun h2 => ?_⟩
  obtain ⟨q', hq', heq⟩ := hpre (by omega)
  simp only [multDom, multPairs, Finset.mem_image, Finset.mem_biUnion, Finset.mem_range]
  exact ⟨q', ⟨d, by omega, by simpa using hq'⟩, heq⟩

/-- The rooted tree `T^s` on the elements of `R^s` (Depian et al., Definition 26, p.24): the parent
of a vertex is the address with the last entry removed, and the depth is the length of the
address. -/
noncomputable def multTree (R : Structure σ V) (T : RootedForest V) (p s : ℕ) :
    RootedForest (MultElem R T p s) where
  parent a :=
    open Classical in
    if h : 2 ≤ a.1.length ∧ a.1.dropLast ∈ multDom R T p s then some ⟨a.1.dropLast, h.2⟩ else none
  depth a := a.1.length
  depth_root a h := by
    have hs := multDom_spec R T p s a.1 a.2
    by_contra hne
    have h2 : 2 ≤ a.1.length := by omega
    rw [dif_pos ⟨h2, hs.2 h2⟩] at h
    exact absurd h (by simp)
  depth_parent a b h := by
    by_cases hc : 2 ≤ a.1.length ∧ a.1.dropLast ∈ multDom R T p s
    · rw [dif_pos hc] at h
      cases h
      simp only [List.length_dropLast]
      omega
    · rw [dif_neg hc] at h
      exact absurd h (by simp)

/-- The **`s`-multiplicity structure** `R^s` for `(R, T, p)` (Depian et al., Definition 26,
pp.24–25), for `s ≥ p ≥ 1`. A tuple `ū` of elements of `R^s` lies in `E_i^s` exactly when its
entries are pairwise in ancestor–descendant relation in `T^s` and `orig ∘ ū ∈ E_i`.

**Formalization Note** (equivalence with Definition 26.) The procedure keeps the tuples of `R`
whose entries are all kept and, at every copy step, adds the image of every current tuple under
the copying bijection; every tuple stays a chain of `T^s` (Lemma 28 (1)) with the same originals.
Conversely, a chain of `T^s` whose originals form a tuple of `E_i` is produced: replacing the
entries inside the outermost copied subtree by their preimages gives a chain created earlier, and
the copy step that created the subtree adds its image. For `s = p` no copies are made and `R^p` is
the substructure of `R` induced by the kept elements (Lemma 28 (5)). -/
noncomputable def mult (R : Structure σ V) (T : RootedForest V) (p s : ℕ) :
    Structure σ (MultElem R T p s) where
  rel i := {u | (∀ j j', (u j).1 <+: (u j').1 ∨ (u j').1 <+: (u j).1) ∧
    (fun j => orig (u j)) ∈ R.rel i}

end Mult

end SNPTreedepth


