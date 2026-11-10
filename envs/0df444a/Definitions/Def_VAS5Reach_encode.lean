-- Prove2me | Definitions.Def_VAS5Reach_encode
-- name    : VAS5Reach_encode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:27:24.026776+00:00
-- url     : https://prove2.me/theorems/f734bde0-5158-4b55-a8de-7921c266a17d
-- title:
--   $B$-encodings $[\![V]\!]_{I,B}$ and $\widehat{[\![V]\!]}_{I,B}$
-- statement:
--   Let $V = (Q, T)$ be a $d$-VASS, $I \subseteq [d]$ and $B \in \mathbb N$. The **$B$-encoding** $[\![V]\!]_{I,B}$ is the $(d - |I|)$-VASS with state set $Q' := Q \times [0, B]^I$ which, for every $(p, a, q) \in T$ and $p(u) \in Q'$, has the transition
--   $$
--   \bigl(p(u),\ a{\restriction}_{[d]\setminus I},\ q(v)\bigr) \quad\text{precisely when}\quad v = u + a{\restriction}_I \in [0, B]^I .
--   $$
--   A configuration $p(x)$ with $x{\restriction}_I \in [0,B]^I$ corresponds to $[\![p(x)]\!]_{I,B} = (p, x{\restriction}_I)(x{\restriction}_{[d]\setminus I})$. The **retained-coordinate encoding** $\widehat{[\![V]\!]}_{I,B}$ (`encodeHat`) has the same states and the transitions $(p(u), a, q(v))$ under the same condition, keeping all $d$ counters.
--
--   The module also defines the box $[0,B]^I$ (`box`), restrictions (`restrictI`, `restrictC`), the map restoring the counter values stored in a state (`decode`), the underlying VAS transition of a transition of an encoding of a VAS (`underlying`: $v - u$ on $I$, the counter effect elsewhere), and the Parikh image of a sequence of vectors (`parikh`: the number of occurrences of each vector). Parikh images of paths of $[\![V]\!]_B$ count their underlying transitions in $T$, as in §4 of the paper.
--
--   **Formalization Note** $I$ is an arbitrary finite set of coordinates and the remaining counters are indexed by the coordinates outside $I$, without renumbering. The paper's $[\![V]\!]_B$ is the case $|I| = 2$ for a VAS (a one-state VASS).
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), §3 'B-Encoding and Sequential VASS', pp.15–16 (PDF pp.17–18); retained-coordinate encoding §6, pp.24–25 (PDF pp.26–27); Parikh images p.13 and §4, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_VAS5Reach_VASS

namespace VAS5Reach

variable {S ι : Type}

open Classical in
/-- The box `[0, B]^I` of values of the encoded coordinates `I`. -/
noncomputable def box (I : Finset ι) (B : ℕ) : Finset (I → ℕ) :=
  Fintype.piFinset fun _ => Finset.range (B + 1)

/-- The restriction `x↾I` of a vector to the coordinates in `I`. -/
def restrictI (I : Finset ι) (x : ι → ℕ) : I → ℕ := fun i => x i.1

/-- The restriction `x↾[d]∖I` of a vector to the coordinates outside `I`. -/
def restrictC (I : Finset ι) (x : ι → ℕ) : {i // i ∉ I} → ℕ := fun i => x i.1

open Classical in
/-- Restoring the counter values stored in a state: from the encoded values `u ∈ [0,B]^I` and the
remaining counters `z`, the vector `x` with `x↾I = u` and `x↾[d]∖I = z`. -/
noncomputable def decode (I : Finset ι) (u : I → ℕ) (z : {i // i ∉ I} → ℕ) : ι → ℕ :=
  fun i => if h : i ∈ I then u ⟨i, h⟩ else z ⟨i, h⟩

open Classical in
/-- The `B`-encoding `[[V]]_{I,B}` of a `d`-VASS `V = (Q, T)` on the coordinates `I`: the
`(d − |I|)`-VASS with state set `Q′ := Q × [0, B]^I` and, for every `(p, a, q) ∈ T` and
`p(u) ∈ Q′`, the transition `(p(u), a↾[d]∖I, q(v))` precisely when `v = u + a↾I ∈ [0, B]^I`.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), §3 "B-Encoding and
Sequential VASS", printed pp. 15–16 (PDF pp. 17–18): "Let V = (Q, T) be a d-VASS, I ⊆ [d], and
B ∈ N. The (d − |I|)-VASS [[V]]_{I,B} has state set Q′ := Q × [0, B]^I. […] For every (p, a, q) ∈ T
and p(u) ∈ Q′, it has the transition (p(u), a↾[d]\I, q(v)) precisely when v = u + a↾I ∈ [0, B]^I.
For p(x) with x↾I ∈ [0, B]^I, set [[p(x)]]_{I,B} = (p, x↾I)(x↾[d]\I)."

**Formalization Note** `I` is an arbitrary `Finset` of coordinates; the counters of the encoding
are the subtype `{i // i ∉ I}` (no renumbering), and a state is a pair `(p, u)` with
`u : I → ℕ`. The configuration `[[p(x)]]_{I,B}` is `(p, restrictI I x)(restrictC I x)`. For a VAS
`V` (a one-state VASS, `VASS.ofVAS`) this is the paper's `B`-encoding `[[V]]_B` when `|I| = 2`. -/
noncomputable def encode (V : VASS S ι) (I : Finset ι) (B : ℕ) :
    VASS (S × (I → ℕ)) {i // i ∉ I} where
  states := V.states ×ˢ box I B
  trans := ((V.trans ×ˢ box I B).filter fun σ =>
      ∀ i : I, 0 ≤ (σ.2 i : ℤ) + σ.1.2.1 i.1 ∧ (σ.2 i : ℤ) + σ.1.2.1 i.1 ≤ B).image
    fun σ => ((σ.1.1, σ.2), fun j => σ.1.2.1 j.1,
      (σ.1.2.2, fun i => ((σ.2 i : ℤ) + σ.1.2.1 i.1).toNat))
  trans_mem := by
    intro τ h
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product] at h
    obtain ⟨σ, ⟨⟨h1, h2⟩, h3⟩, rfl⟩ := h
    refine ⟨Finset.mem_product.mpr ⟨(V.trans_mem _ h1).1, h2⟩,
      Finset.mem_product.mpr ⟨(V.trans_mem _ h1).2, ?_⟩⟩
    simp only [box, Fintype.mem_piFinset, Finset.mem_range]
    intro i
    have := h3 i
    omega

open Classical in
/-- The retained-coordinate encoding `[[V]]^_{I,B}` (with a hat): the same state set
`Q × [0, B]^I` as `[[V]]_{I,B}`, but all `d` coordinates are retained: for every `(p, a, q) ∈ T`
and `p(u) ∈ Q′` it has the transition `(p(u), a, q(v))` precisely when `v = u + a↾I ∈ [0, B]^I`.

Source: arXiv:2610.40012 (held version, sha256 a74d76f9…), §6, printed pp. 24–25
(PDF pp. 26–27): "We also use [[V]]^_{I,B}, with the same state set but retaining all d
coordinates. For every (p, a, q) ∈ T and p(u) ∈ Q′, it has the transition (p(u), a, q(v)) precisely
when v = u + a↾I ∈ [0, B]^I." -/
noncomputable def encodeHat (V : VASS S ι) (I : Finset ι) (B : ℕ) : VASS (S × (I → ℕ)) ι where
  states := V.states ×ˢ box I B
  trans := ((V.trans ×ˢ box I B).filter fun σ =>
      ∀ i : I, 0 ≤ (σ.2 i : ℤ) + σ.1.2.1 i.1 ∧ (σ.2 i : ℤ) + σ.1.2.1 i.1 ≤ B).image
    fun σ => ((σ.1.1, σ.2), σ.1.2.1,
      (σ.1.2.2, fun i => ((σ.2 i : ℤ) + σ.1.2.1 i.1).toNat))
  trans_mem := by
    intro τ h
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product] at h
    obtain ⟨σ, ⟨⟨h1, h2⟩, h3⟩, rfl⟩ := h
    refine ⟨Finset.mem_product.mpr ⟨(V.trans_mem _ h1).1, h2⟩,
      Finset.mem_product.mpr ⟨(V.trans_mem _ h1).2, ?_⟩⟩
    simp only [box, Fintype.mem_piFinset, Finset.mem_range]
    intro i
    have := h3 i
    omega

open Classical in
/-- The underlying transition vector in `ℤ^d` of a transition `(p(u), a′, q(v))` of an encoding
`[[V]]_{I,B}` of a VAS: `v − u` on the encoded coordinates `I` and `a′` elsewhere. For an encoding
of a VAS this is the VAS transition `a ∈ T` that induced it. -/
noncomputable def underlying (I : Finset ι)
    (τ : (S × (I → ℕ)) × ({i // i ∉ I} → ℤ) × (S × (I → ℕ))) : ι → ℤ :=
  fun i => if h : i ∈ I then ((τ.2.2.2 ⟨i, h⟩ : ℕ) : ℤ) - ((τ.1.2 ⟨i, h⟩ : ℕ) : ℤ)
    else τ.2.1 ⟨i, h⟩

open Classical in
/-- The Parikh image of a sequence of transition vectors: `ψ_w(a)` is the number of occurrences
of `a` in `w`. Parikh images of paths of an encoding `[[V]]_B` of a VAS are taken of the sequence
of their underlying VAS transitions (`underlying`).

Source: arXiv:2610.40012 (held version, sha256 a74d76f9…), §3, printed p. 13 (PDF p. 15): "The
Parikh image of a path π ∈ T∗ is the vector ψπ ∈ N^m whose i-th component counts the number of
occurrences of ui in π. […] We also write ψπ(u) for the number of occurrences of a transition
u ∈ T in π when the chosen enumeration is irrelevant"; §4, printed p. 17 (PDF p. 19):
"Throughout this section, Parikh images of paths in [[V]]_B count their underlying transitions in
T."

**Formalization Note** The Parikh image is a function from vectors to `ℕ` (counts), which is the
paper's `ψ_π(u)` without an enumeration of `T`. -/
noncomputable def parikh (w : List (ι → ℤ)) : (ι → ℤ) → ℕ :=
  fun a => w.count a

end VAS5Reach


