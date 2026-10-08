-- Prove2me | Definitions.Def_BartlettNN_FatNet_coverNum
-- name    : BartlettNN_FatNet_coverNum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T18:25:22.347753+00:00
-- url     : https://prove2.me/theorems/888b3eb2-9df8-4f4d-9f78-643a4d694999
-- title:
--   Sample pseudometrics d_{ℓ1(x)}, d_{ℓ2(x)} and covering numbers N_1, N_2 (Definition 18)
-- statement:
--   Let $(S,\rho)$ be a pseudometric space. For $A\subseteq S$, a set $T\subseteq S$ is an **$\varepsilon$-cover** of $A$ with respect to $\rho$ if for every $a\in A$ there is $t\in T$ with $\rho(t,a)<\varepsilon$; $\mathcal N(A,\varepsilon,\rho)$ is the size of the smallest $\varepsilon$-cover of $A$. Here $S$ is the set of all real-valued functions on a set $X$, so a cover need not consist of members of $A$.
--
--   For a sample $x=(x_1,\dots,x_m)\in X^m$ define the pseudometrics
--
--   $$
--   d_{\ell_\infty(x)}(f,g)=\max_i|f(x_i)-g(x_i)|,\qquad
--   d_{\ell_1(x)}(f,g)=\frac1m\sum_{i=1}^m|f(x_i)-g(x_i)|,\qquad
--   d_{\ell_2(x)}(f,g)=\Big(\frac1m\sum_{i=1}^m(f(x_i)-g(x_i))^2\Big)^{1/2},
--   $$
--
--   and for a class $F$ of functions on $X$
--
--   $$
--   \mathcal N_p(F,\varepsilon,m)=\max_{x\in X^m}\mathcal N(F,\varepsilon,d_{\ell_p(x)}),\qquad p\in\{\infty,1,2\}.
--   $$
--
--   These are the uniform (worst-sample) covering numbers through which the fat-shattering dimension of a network class is bounded.
--
--   **Formalization Note** This module defines $d_{\ell_1(x)}$, $d_{\ell_2(x)}$, $\mathcal N_1$ and $\mathcal N_2$; the covering number `coverNum`, $d_{\ell_\infty(x)}$ (`dInf`) and $\mathcal N_\infty$ (`Ninf`) are those of `BartlettNN.Margin.Covering`, which it imports and which are recalled above for completeness. `coverNum d F ε` is the infimum, over finite sets `T` of functions $X\to\mathbb R$ such that every $f\in F$ has some $g\in T$ with `d g f < ε` (strict), of the cardinality of `T`, valued in $\mathbb N_\infty$; it is $\infty$ when no finite $\varepsilon$-cover exists. `N1` and `N2` take the supremum of `coverNum` over all samples `x : Fin m → X`. In Lean $1/0=0$, so for $m=0$ the $\ell_1$ and $\ell_2$ distances are $0$; the paper always has $m\ge1$ where it matters.
-- source:
--   Bartlett, The Sample Complexity of Pattern Classification with Neural Networks, IEEE Trans. Inform. Theory 44 (1998), p. 527, Definition 3 and the definition of d_{ℓ∞(x)}, N_∞; p. 532, Definition 18

import Mathlib
import Definitions.Def_BartlettNN_Margin_Covering

namespace BartlettNN.FatNet

/-- Bartlett (1998), Definition 18, p. 532:
`d_{ℓ1(x)}(f, g) = (1/m) ∑_{i=1}^m |f(x_i) − g(x_i)|`. -/
noncomputable def dL1 {X : Type*} {m : ℕ} (x : Fin m → X) (f g : X → ℝ) : ℝ :=
  (1 / (m : ℝ)) * ∑ i, |f (x i) - g (x i)|

/-- Bartlett (1998), Definition 18, p. 532:
`d_{ℓ2(x)}(f, g) = ((1/m) ∑_{i=1}^m (f(x_i) − g(x_i))²)^{1/2}`. -/
noncomputable def dL2 {X : Type*} {m : ℕ} (x : Fin m → X) (f g : X → ℝ) : ℝ :=
  Real.sqrt ((1 / (m : ℝ)) * ∑ i, (f (x i) - g (x i)) ^ 2)

/-- `N_1(F, ε, m) = max_{x ∈ X^m} N(F, ε, d_{ℓ1(x)})` (Definition 18, p. 532). -/
noncomputable def N1 {X : Type*} (F : Set (X → ℝ)) (ε : ℝ) (m : ℕ) : ℕ∞ :=
  ⨆ x : Fin m → X, BartlettNN.Margin.coverNum (dL1 x) F ε

/-- `N_2(F, ε, m) = max_{x ∈ X^m} N(F, ε, d_{ℓ2(x)})` (Definition 18, p. 532). -/
noncomputable def N2 {X : Type*} (F : Set (X → ℝ)) (ε : ℝ) (m : ℕ) : ℕ∞ :=
  ⨆ x : Fin m → X, BartlettNN.Margin.coverNum (dL2 x) F ε

end BartlettNN.FatNet


