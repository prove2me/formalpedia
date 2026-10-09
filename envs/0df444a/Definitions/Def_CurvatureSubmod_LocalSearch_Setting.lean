-- Prove2me | Definitions.Def_CurvatureSubmod_LocalSearch_Setting
-- name    : CurvatureSubmod_LocalSearch_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T10:08:19.735979+00:00
-- url     : https://prove2.me/theorems/0006e430-63af-41ef-bb2a-0e37a3fdda86
-- title:
--   §2.1, (1.1), §3, §5.1, §6 — marginal values, monotonicity, total curvature, the potentials h and ψ, swap-local optima, and the decompositions (ℓ, g)
-- statement:
--   Throughout, $X$ is a finite ground set and a set function is a map $f : 2^X \to \mathbb{R}$. This file collects the objects of Sviridenko, Vondrák and Ward used for submodular maximization and supermodular minimization under bounded curvature.
--
--   1. **Marginal value** (§2.1). For $A \subseteq X$ and $i \in X$,
--   $$f_A(i) = f(A + i) - f(A).$$
--   (For $i \in A$ this is $0$.)
--   2. **Monotonicity** (§2.1). $f$ is *monotone increasing* (non-decreasing) if $f_A(i) \ge 0$ for all $i \in X$ and $A \subseteq X$, and *monotone decreasing* (non-increasing) if $f_A(i) \le 0$ for all $i$, $A$.
--   3. **Supermodularity** (§2.1). $f$ is supermodular if $-f$ is submodular, i.e. $f(A) + f(B) \le f(A \cap B) + f(A \cup B)$ for all $A, B \subseteq X$.
--   4. **Total curvature at most $c$** ((1.1), p. 3). For a monotone increasing $f$: $f_{X-j}(j) \ge (1-c)\, f_\emptyset(j)$ for every $j \in X$. For a monotone decreasing $f$: $f_{X-j}(j) \le (1-c)\, f_\emptyset(j)$ for every $j \in X$.
--   5. **Linear functions** (§3). For weights $w : X \to \mathbb{R}$, $\ell(A) = \sum_{j \in A} w(j)$.
--   6. **Filmus–Ward potential** (§5.1, p. 7). For a set function $g$,
--   $$h(A) = \sum_{\emptyset \ne B \subseteq A} g(B) \int_0^1 \frac{e^p}{e-1}\, p^{|B|-1} (1-p)^{|A|-|B|}\, dp .$$
--   7. **Local-search potential** (§5.1, p. 7). $\psi(A) = (1 - e^{-1})\, h(A) + \ell(A)$.
--   8. **Swap-local optimum** (§5.1, p. 7, paragraph after the proof of Lemma 5.2; the exchanges are those of Figure 4). For a matroid $\mathcal M$ on $X$ and a potential $\varphi$, a set $S$ is locally optimal for $\varphi$ under single-element exchanges if $S$ is a base of $\mathcal M$ and $\varphi(S) - \varphi(S - a + b) \ge 0$ for every $a \in S$, $b \in X \setminus S$ with $S - a + b$ a base of $\mathcal M$.
--   9. **Decomposition for maximization** (§6.1, p. 8). $\ell(A) = \sum_{j \in A} f_{X-j}(j)$ and $g(A) = f(A) - \ell(A)$.
--   10. **Decomposition for minimization** (§6.2, p. 9). $\ell(A) = \sum_{j \in A} f_\emptyset(j)$ and $g(A) = -\ell(A) - f(X \setminus A)$.
--
--   These are the objects in which the paper's reduction is phrased: a function of bounded curvature is split as $f = g + \ell$ with $g$ monotone submodular and $\ell$ linear, and a non-oblivious local search guided by $\psi$ approximates $g + \ell$ over the bases of a matroid.
--
--   **Formalization Note** Subsets of $X$ are `Finset X` over a `Fintype X`; $X - j$ is `Finset.univ.erase j` and $A + i$ is `insert i A`. Submodularity is the published definition `NonmonotoneSubmod.Shared.Submodular`. Total curvature is stated in the product form used by the paper's own proofs (p. 14) instead of the ratio of (1.1): the two agree whenever every $f_\emptyset(j) \ne 0$, and the product form avoids Lean's convention $x/0 = 0$. The paper's sum defining $h$ runs over all $B \subseteq A$; its $B = \emptyset$ term has the factor $\int_0^1 p^{-1}\cdots\,dp = \infty$ and only makes sense under Filmus and Ward's normalisation $g(\emptyset) = 0$, where it vanishes. Here it is excluded explicitly; the constant $g(\emptyset)$ then contributes to $h(A)$ only through $|A|$, so it does not affect any swap comparison. The matroid is Mathlib's `Matroid X`.
-- source:
--   Sviridenko, Vondrák, Ward, Optimal approximation for submodular and supermodular optimization with bounded curvature (SODA 2015 version, Oct. 9, 2014), pp. 3–9, (1.1) p. 3, §2.1 p. 4, §3 p. 5, §5.1 and Figure 4 p. 7, §6.1 p. 8, §6.2 p. 9

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

namespace CurvatureSubmod.LocalSearch

variable {X : Type} [Fintype X] [DecidableEq X]

/-- §2.1, p. 4: the marginal value `f_A(i) = f(A + i) − f(A)`. -/
def marg (f : Finset X → ℝ) (A : Finset X) (i : X) : ℝ := f (insert i A) - f A

/-- §2.1, p. 4: `f` is non-decreasing (monotone increasing): `f_A(i) ≥ 0` for all `i`, `A`. -/
def MonoInc (f : Finset X → ℝ) : Prop := ∀ (A : Finset X) (i : X), 0 ≤ marg f A i

/-- §2.1, p. 4: `f` is non-increasing (monotone decreasing): `f_A(i) ≤ 0` for all `i`, `A`. -/
def MonoDec (f : Finset X → ℝ) : Prop := ∀ (A : Finset X) (i : X), marg f A i ≤ 0

/-- §2.1, p. 4: `f` is supermodular iff `−f` is submodular. -/
def Supermodular (f : Finset X → ℝ) : Prop :=
  NonmonotoneSubmod.Shared.Submodular (fun A => - f A)

/-- (1.1), p. 3, product form: a monotone increasing `f` has total curvature at most `c` when
`f_{X−j}(j) ≥ (1 − c) f_∅(j)` for every `j`. -/
def CurvAtMostInc (f : Finset X → ℝ) (c : ℝ) : Prop :=
  ∀ j : X, (1 - c) * marg f ∅ j ≤ marg f (Finset.univ.erase j) j

/-- (1.1) with Lemma 2.2's proof, p. 14, product form: a monotone decreasing `f` has total
curvature at most `c` when `f_{X−j}(j) ≤ (1 − c) f_∅(j)` for every `j`. -/
def CurvAtMostDec (f : Finset X → ℝ) (c : ℝ) : Prop :=
  ∀ j : X, marg f (Finset.univ.erase j) j ≤ (1 - c) * marg f ∅ j

/-- §3, p. 5: the linear function `ℓ(A) = Σ_{j ∈ A} ℓ(j)` with weights `ℓ(j) = w j`. -/
def linFun (w : X → ℝ) (A : Finset X) : ℝ := ∑ j ∈ A, w j

/-- §5.1, p. 7: Filmus and Ward's potential
`h(A) = Σ_{∅ ≠ B ⊆ A} g(B) ∫₀¹ e^p/(e − 1) · p^{|B|−1} (1 − p)^{|A|−|B|} dp`
(the term `B = ∅` is excluded, see the natural-language statement). -/
noncomputable def hPot (g : Finset X → ℝ) (A : Finset X) : ℝ :=
  ∑ B ∈ A.powerset.filter (fun B => B.Nonempty),
    g B * ∫ p in (0:ℝ)..1,
      Real.exp p / (Real.exp 1 - 1) * p ^ (B.card - 1) * (1 - p) ^ (A.card - B.card)

/-- §5.1, p. 7: the local-search potential `ψ(A) = (1 − e^{−1}) h(A) + ℓ(A)`. -/
noncomputable def psi (g : Finset X → ℝ) (w : X → ℝ) (A : Finset X) : ℝ :=
  (1 - Real.exp (-1)) * hPot g A + linFun w A

/-- §5.1, p. 7, paragraph after the proof of Lemma 5.2 (the exchanges of Figure 4): `S` is a base
of `M` that is locally optimal for `φ` under single-element exchanges, i.e. `φ(S) − φ(S − a + b) ≥ 0`
for every `a ∈ S`, `b ∉ S` with `S − a + b` a base. -/
def IsSwapLocalOpt (M : Matroid X) (φ : Finset X → ℝ) (S : Finset X) : Prop :=
  M.IsBase (↑S : Set X) ∧
    ∀ a ∈ S, ∀ b : X, b ∉ S → M.IsBase (↑(insert b (S.erase a)) : Set X) →
      φ (insert b (S.erase a)) ≤ φ S

/-- §6.1, p. 8: the weights `ℓ(j) = f_{X−j}(j)` of the linear part. -/
def wMax (f : Finset X → ℝ) (j : X) : ℝ := marg f (Finset.univ.erase j) j

/-- §6.1, p. 8: `g(A) = f(A) − ℓ(A)` with `ℓ(A) = Σ_{j∈A} f_{X−j}(j)`. -/
def gMax (f : Finset X → ℝ) (A : Finset X) : ℝ := f A - linFun (wMax f) A

/-- §6.2, p. 9: the weights `ℓ(j) = f_∅(j)` of the linear part. -/
def wMin (f : Finset X → ℝ) (j : X) : ℝ := marg f ∅ j

/-- §6.2, p. 9: `g(A) = −ℓ(A) − f(X ∖ A)` with `ℓ(A) = Σ_{j∈A} f_∅(j)`. -/
def gMin (f : Finset X → ℝ) (A : Finset X) : ℝ :=
  - linFun (wMin f) A - f (Finset.univ \ A)

end CurvatureSubmod.LocalSearch


