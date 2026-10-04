-- Prove2me | Definitions.Def_BalcanDDA_Piecewise_dual
-- name    : BalcanDDA_Piecewise_dual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T05:57:39.67726+00:00
-- url     : https://prove2.me/theorems/51190914-44e5-4840-a03e-0d9455644839
-- title:
--   Dual class $\mathcal H^*$ of a function class (Definition 3.1)
-- statement:
--   Let $\mathcal Y$ be a domain and $\mathcal H \subseteq \mathbb R^{\mathcal Y}$ a set of real-valued functions on $\mathcal Y$. For each input $y \in \mathcal Y$, the **dual function** $h^*_y : \mathcal H \to \mathbb R$ evaluates a function at $y$:
--   $$h^*_y(h) = h(y) \qquad (h \in \mathcal H).$$
--   The **dual class** of $\mathcal H$ is the set of all such evaluation maps,
--   $$\mathcal H^* = \{\, h^*_y : \mathcal H \to \mathbb R \mid y \in \mathcal Y \,\}.$$
--   The class $\mathcal H$ is called the **primal class**. The same construction applies verbatim to a class $\mathcal G \subseteq \{0,1\}^{\mathcal Y}$ of binary-valued functions, giving $\mathcal G^* = \{ g^*_y : \mathcal G \to \{0,1\} \mid y \in \mathcal Y\}$.
--
--   In data-driven algorithm design, if $\mathcal U = \{u_\rho\}$ is the class of utility functions of a parameterized algorithm on problem instances $\mathcal X$, then the dual function $u^*_x$ records how the performance on one fixed instance $x$ varies with the algorithm; the paper's main theorem bounds the pseudo-dimension of $\mathcal U$ through the structure of $\mathcal U^*$.
--
--   **Formalization Note.** The domain of every dual function is the class itself, taken as the subtype $\uparrow\mathcal H$, not a parameter space. `dual` handles real-valued classes and `dualB` binary-valued ones, with $\{0,1\}$ represented by `Bool` ($\mathrm{true} \leftrightarrow 1$).
-- source:
--   Balcan et al., How Much Data Is Sufficient to Learn High-Performing Algorithms?, arXiv:1908.02894v4, p. 7, Definition 3.1

import Mathlib

namespace BalcanDDA.Piecewise

/-- The dual class of a real-valued function class (Balcan et al., *How Much Data Is Sufficient
to Learn High-Performing Algorithms?*, arXiv:1908.02894v4, p. 7, Definition 3.1).
For `H ⊆ ℝ^Y`, `H* = {h*_y : H → ℝ | y ∈ Y}` with `h*_y(h) = h(y)`. The domain of each dual
function is the class `H` itself, taken as the subtype `↥H`. -/
def dual {Y : Type*} (H : Set (Y → ℝ)) : Set (↥H → ℝ) :=
  Set.range fun (y : Y) (h : ↥H) => (h : Y → ℝ) y

/-- The dual class of a `{0,1}`-valued function class (Definition 3.1, p. 7, applied to a class
`G ⊆ {0,1}^Y`; `{0,1}` is `Bool` with `true ↔ 1`): `G* = {g*_y : G → {0,1} | y ∈ Y}` with
`g*_y(g) = g(y)`. -/
def dualB {Y : Type*} (G : Set (Y → Bool)) : Set (↥G → Bool) :=
  Set.range fun (y : Y) (g : ↥G) => (g : Y → Bool) y

end BalcanDDA.Piecewise


