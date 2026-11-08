-- Prove2me | Definitions.Def_AsymSpecConn_Spectrum
-- name    : AsymSpecConn_Spectrum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:38:58.755788+00:00
-- url     : https://prove2.me/theorems/04313296-eaf4-4d3d-bdbd-b7aa091cc5fb
-- title:
--   The asymptotic spectrum $\Delta$ of a preordered semiring
-- statement:
--   Let $\mathcal S$ be a commutative semiring with a preorder $\le$. Its **asymptotic spectrum** $\Delta$ is the set of all semiring homomorphisms $f:\mathcal S\to\mathbb R_{\ge0}$ with $f(1)=1$ that are monotone: $s\le t$ implies $f(s)\le f(t)$. The elements of $\Delta$ are the **spectral points**. $\Delta$ carries the topology of pointwise convergence, the coarsest topology making $f\mapsto f(s)$ continuous for every $s\in\mathcal S$.
--
--   For $s_1,\dots,s_q\in\mathcal S$ the module also defines the **value set**
--   $$\Delta(s_1,\dots,s_q)=\{(g(s_1),\dots,g(s_q)):g\in\Delta\}\subseteq\mathbb R^q.$$
--
--   **Formalization Note** $\Delta$ is a subset of the function space $\mathcal S\to\mathbb R_{\ge0}$, and the space $\Delta$ is the subtype with the subspace topology of the product topology, which is exactly pointwise convergence.
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), §2, p.12; value set: Corollary 2.11, p.18

import Mathlib

set_option autoImplicit false

open scoped NNReal

namespace AsymSpecConn

/-- **The asymptotic spectrum** `Δ` (§2, p.12 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)).

`Spectrum S P` is the set of all semiring homomorphisms `f : S → ℝ≥0` (so `f 0 = 0`,
`f 1 = 1`, `f (s + t) = f s + f t`, `f (s * t) = f s * f t`) that are monotone for `P`:
`s ≤ t` implies `f s ≤ f t`. Its elements are the *spectral points*.

**Formalization Note** `Δ` is a subset of the function space `S → ℝ≥0`; the space `Δ` is the
subtype `↥(Spectrum S P)` with the subspace topology of the product topology, i.e. the
topology of pointwise convergence (the coarsest topology making every evaluation
`f ↦ f s` continuous), as on p.12. -/
def Spectrum (S : Type*) [CommSemiring S] (P : Preorder S) : Set (S → ℝ≥0) :=
  {f | f 0 = 0 ∧ f 1 = 1 ∧ (∀ s t, f (s + t) = f s + f t) ∧ (∀ s t, f (s * t) = f s * f t) ∧
    ∀ s t, P.le s t → f s ≤ f t}

/-- **The value set** `Δ(s₁, …, s_q) = {(g(s₁), …, g(s_q)) : g ∈ Δ} ⊆ ℝ^q`
(Corollary 2.11, p.18 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)). For `q = 1` this is
`Δ(s) = {g(s) : g ∈ Δ}` (identified with a subset of `ℝ` via `Fin 1 → ℝ`). -/
def valueSet (S : Type*) [CommSemiring S] (P : Preorder S) {q : ℕ} (s : Fin q → S) :
    Set (Fin q → ℝ) :=
  Set.range (fun g : ↥(Spectrum S P) => fun j => ((g.1 (s j) : ℝ≥0) : ℝ))

end AsymSpecConn


