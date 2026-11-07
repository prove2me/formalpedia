-- Prove2me | Definitions.Def_OnlineCAP_HasSCC
-- name    : OnlineCAP_HasSCC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:23:47.584935+00:00
-- url     : https://prove2.me/theorems/905017e3-1223-4650-b82e-9029d433c7c5
-- title:
--   Shallow traces and shallow cell complexity
-- statement:
--   Let $\mathcal G$ be a family of finite subsets of a universe $V$. For $W\subseteq V$ the **trace** of $\mathcal G$ on $W$ is $\mathcal G|_W=\{Q\cap W:Q\in\mathcal G\}$, and for an integer $\kappa\ge1$ a trace $S$ is **$\kappa$-shallow** if $1\le|S|\le\kappa$.
--
--   The set system $(V,\mathcal G)$ has **shallow cell complexity** $\varphi$ if for every finite $W\subseteq V$ and every integer $\kappa\ge1$,
--   $$\big|\{S\in\mathcal G|_W : 1\le|S|\le\kappa\}\big|\le|W|\cdot\varphi(|W|,\kappa).$$
--
--   Traces are counted as distinct sets.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Definition 4.2, p.14

import Mathlib

namespace OnlineCAP

/-- **κ-shallow traces of a set system.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Definition 4.2, items 1–2, p.14 (PDF p.14):
"For any subset W ⊆ V, the trace of G on W is the family of induced subsets G|W := {Q ∩ W : Q ∈ G}.
… For an integer κ ≥ 1, a trace S ∈ G|W is called a κ-shallow trace if we have 1 ≤ |S| ≤ κ."

`shallowTraces G W κ` is the finite set of **distinct** traces `Q ∩ W`, `Q ∈ G`, with
`1 ≤ |Q ∩ W| ≤ κ`. -/
noncomputable def shallowTraces {V : Type} [DecidableEq V] (G : Set (Finset V)) (W : Finset V)
    (κ : ℕ) : Finset (Finset V) := by
  classical
  exact W.powerset.filter (fun S => (∃ Q ∈ G, Q ∩ W = S) ∧ 1 ≤ S.card ∧ S.card ≤ κ)

/-- **Shallow cell complexity.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Definition 4.2, item 3, p.14 (PDF p.14): "We say that
(V, G) has shallow cell complexity φ (for function φ : N × N → R≥0), if for every subset W ⊆ V
with |W| = m, |{S ∈ G|W : 1 ≤ |S| ≤ κ}| ≤ m · φ(m, κ)."

For every finite `W` and every integer `κ ≥ 1`, the number of distinct κ-shallow traces on `W` is
at most `|W| · φ(|W|, κ)`.

**Formalization Note.** The set system is a family `G` of finite subsets of `V`; `φ` is
real-valued (the bounds used are nonnegative). -/
def HasSCC {V : Type} [DecidableEq V] (G : Set (Finset V)) (φ : ℕ → ℕ → ℝ) : Prop :=
  ∀ (W : Finset V) (κ : ℕ), 1 ≤ κ → ((shallowTraces G W κ).card : ℝ) ≤ W.card * φ W.card κ

end OnlineCAP


