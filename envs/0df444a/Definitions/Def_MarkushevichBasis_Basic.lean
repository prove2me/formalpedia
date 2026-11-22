-- Prove2me | Definitions.Def_MarkushevichBasis_Basic
-- name    : MarkushevichBasis_Basic
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T18:48:42.8038+00:00
-- url     : https://prove2.me/theorems/799129dc-5a8b-42ba-a6b4-c7a691282dce
-- title:
--   Markushevich basis (fundamental and total biorthogonal system) of a topological vector space
-- statement:
--   **Markushevich basis.** Let $\mathbb K$ be a nontrivially normed field (in the paper $\mathbb K=\mathbb C$), let $E$ be a topological vector space over $\mathbb K$ with continuous dual $E'$, and let $\iota$ be an index set. A family of pairs $\{(x_i,f_i)\}_{i\in\iota}$ with $x_i\in E$ and $f_i\in E'$ is a *Markushevich basis* (M-basis) of $E$ if
--
--   1. it is **biorthogonal**: $f_i(x_j)=\delta_{ij}$ for all $i,j\in\iota$;
--   2. it is **fundamental** (complete): the linear span of the $x_i$ is dense in $E$,
--   $$\overline{\operatorname{span}}\{x_i : i\in\iota\}=E;$$
--   3. it is **total**: the functionals $f_i$ separate the points of $E$,
--   $$f_i(u)=0\ \text{ for all } i\in\iota\ \Longrightarrow\ u=0,$$
--   when $E'$ separates the points of $E$ (e.g. for $E$ a Hausdorff locally convex space over $\mathbb K=\mathbb R$ or $\mathbb C$, by the Hahn–Banach theorem) this is equivalent to the $\sigma(E',E)$-density of the linear span of the $f_i$ in $E'$.
--
--   Every Schauder basis of a Hausdorff topological vector space, together with its coefficient functionals, is a Markushevich basis, but not conversely: the trigonometric system is a Markushevich basis of $L^1(\mathbb T)$ and of $C(\mathbb T)$ without being a Schauder basis there. In the paper (§10.2) Markushevich bases take over the role of Schauder bases when the locally convex topology of the spaces of adelic theta functions is coarsened to Hilbert–Sobolev norm topologies; the "spectral Markushevich bases" of Chapter 10 are meant in this sense.
--
--   **Deviation from the source.** The paper's description on pp. 311–312 (the span of the $x_m$ is dense and the span of the $f_m$ separates the points of $E$) does not repeat biorthogonality, which is part of the classical notion and of the paper's own usage (p. 438, where $\{f_m\}$ is "the bi-orthogonal sequence", and Remark 10.2.1.2).
--
--   **Formalization Note.** `MarkushevichBasis.IsMarkushevichBasis x f` for `x : ι → E` and `f : ι → StrongDual 𝕜 E` (continuous linear functionals; no topology on the dual is used). Biorthogonality is split into its diagonal part `f i (x i) = 1` and its off-diagonal part `f i (x j) = 0` for `i ≠ j`, which avoids decidability assumptions on `ι`. The index type is arbitrary: the paper uses sequences $(x_m,f_m)_{m\ge 0}$, and arbitrary index sets are the standard setting for non-separable spaces. The Lean predicate is stated for an arbitrary topology on the $\mathbb K$-module $E$; it is intended for topological vector spaces.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 438, §10.2 (opening paragraph), Remark 10.2.1.2 (p. 440), and pp. 311–312 (introduction to Chapter 7); classical reference: H. Jarchow, Locally Convex Spaces, B. G. Teubner, Stuttgart, 1981, Part II, Ch. 14, §14.1, p. 289 (as cited by the paper on p. 312)

import Mathlib

/-!
# Markushevich bases

A *Markushevich basis* (M-basis) of a topological vector space `E` is a biorthogonal system
`(x_i, f_i)_{i ∈ ι}` in `E × E'` which is *fundamental* (the linear span of the `x_i` is dense in
`E`) and *total* (the `f_i` separate the points of `E`).

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026), §10.2, p. 438, and
Remark 10.2.1.2, p. 440; the notion is recalled on pp. 311–312 with a reference to
H. Jarchow, *Locally Convex Spaces*, Part II, Ch. 14, §14.1, p. 289.
-/

namespace MarkushevichBasis

/-- `(x_i, f_i)_{i ∈ ι}` is a Markushevich basis of the topological vector space `E`: the system
is biorthogonal (`f_i (x_i) = 1` and `f_i (x_j) = 0` for `i ≠ j`), the linear span of the vectors
`x_i` is dense in `E`, and the continuous linear functionals `f_i` are total, i.e. the only vector
annihilated by every `f_i` is `0`. -/
structure IsMarkushevichBasis {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] {ι : Type*}
    (x : ι → E) (f : ι → StrongDual 𝕜 E) : Prop where
  /-- Biorthogonality, diagonal part: `f_i (x_i) = 1`. -/
  apply_self : ∀ i, f i (x i) = 1
  /-- Biorthogonality, off-diagonal part: `f_i (x_j) = 0` for `i ≠ j`. -/
  apply_of_ne : ∀ i j, i ≠ j → f i (x j) = 0
  /-- Fundamentality: the linear span of the `x_i` is dense in `E`. -/
  dense_span : Dense (Submodule.span 𝕜 (Set.range x) : Set E)
  /-- Totality: the functionals `f_i` separate the points of `E`. -/
  total : ∀ u : E, (∀ i, f i u = 0) → u = 0

end MarkushevichBasis


