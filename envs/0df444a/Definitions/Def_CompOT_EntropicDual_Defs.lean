-- Prove2me | Definitions.Def_CompOT_EntropicDual_Defs
-- name    : CompOT_EntropicDual_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:32:22.737031+00:00
-- url     : https://prove2.me/theorems/a6355867-dc68-43f1-8583-50165a1b0805
-- title:
--   Discrete couplings, entropy, entropic primal and dual objectives, Gibbs kernel, and log-domain updates
-- statement:
--   Let $a\in\Sigma_n$ and $b\in\Sigma_m$ be probability histograms and let $C\in\mathbb R^{n\times m}$ be a cost matrix. The **coupling set** $U(a,b)$ consists of nonnegative matrices $P$ whose row sums are $a$ and whose column sums are $b$. Write $\langle C,P\rangle=\sum_{i,j}C_{ij}P_{ij}$. The **entropy** and **regularized objective** are
--
--   $$
--   H(P)=-\sum_{i,j}P_{ij}(\log P_{ij}-1),\qquad F_\varepsilon(P)=\langle C,P\rangle-\varepsilon H(P),
--   $$
--
--   with $0\log 0=0$. An entropic optimum is a coupling attaining the minimum of $F_\varepsilon$ on $U(a,b)$; $L_C(a,b)$ is the minimum of the unregularized pairing. The **Gibbs kernel** and **entropic dual objective** are
--
--   $$
--   K_{ij}=e^{-C_{ij}/\varepsilon},\qquad Q(f,g)=\langle f,a\rangle+\langle g,b\rangle-\varepsilon\sum_{i,j}e^{f_i/\varepsilon}K_{ij}e^{g_j/\varepsilon}.
--   $$
--
--   The file also defines feasible Kantorovich potentials by $f_i+g_j\le C_{ij}$ and the two log-domain block updates $f_i=\varepsilon\log a_i-\varepsilon\log\sum_jK_{ij}e^{g_j/\varepsilon}$ and $g_j=\varepsilon\log b_j-\varepsilon\log\sum_iK_{ij}e^{f_i/\varepsilon}$. These objects support the duality and Sinkhorn milestones.
--
--   **Formalization Note** Indices use `Fin n` and `Fin m`; the real infimum defining $L_C$ is used only under simplex hypotheses. Logarithms and division are used in theorems only when their inputs and $\varepsilon$ have the required positivity. Entropy is applied only to nonnegative couplings.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), (2.10)–(2.11), pp. 370–371; (2.21), p. 382; (4.1)–(4.2), p. 425; Gibbs kernel, p. 428; (4.30), p. 448; (4.35)–(4.36), p. 449. https://doi.org/10.1561/2200000073

import Mathlib
import Definitions.Def_CompOT_Assignment_Defs
import Definitions.Def_CompOT_EntropicLimit_Defs

namespace CompOT.EntropicDual

/-- The objective of the regularized primal problem (4.2). -/
noncomputable def entropicObj {n m : ℕ} (C P : Matrix (Fin n) (Fin m) ℝ)
    (ε : ℝ) : ℝ := CompOT.Assignment.frob C P - ε * CompOT.EntropicLimit.entropy P

/-- The Gibbs kernel `Kᵢⱼ = exp(-Cᵢⱼ/ε)` on p. 428. -/
noncomputable def gibbs {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (ε : ℝ) (i : Fin n) (j : Fin m) : ℝ :=
  Real.exp (-C i j / ε)

/-- The unconstrained entropic dual objective in (4.30). -/
noncomputable def dualObjEnt {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ)
    (f : Fin n → ℝ) (g : Fin m → ℝ) : ℝ :=
  (∑ i, f i * a i) + (∑ j, g j * b j) -
    ε * ∑ i, ∑ j, Real.exp (f i / ε) * gibbs C ε i j * Real.exp (g j / ε)

/-- The feasible Kantorovich potentials `R(C)` of (2.21). -/
def KantorovichFeasible {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (f : Fin n → ℝ) (g : Fin m → ℝ) : Prop :=
  ∀ i j, f i + g j ≤ C i j

/-- The unregularized Kantorovich cost `L_C(a,b)` of (2.11).
Only used with probability marginals, when the feasible set is nonempty and compact. -/
noncomputable def unregCost {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ) : ℝ :=
  ⨅ P : CompOT.Assignment.couplings a b, CompOT.Assignment.frob C P.1

/-- The log-domain `f` update in (4.35). -/
noncomputable def updateF {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (ε : ℝ) (g : Fin m → ℝ) (i : Fin n) : ℝ :=
  ε * Real.log (a i) -
    ε * Real.log (∑ j, gibbs C ε i j * Real.exp (g j / ε))

/-- The log-domain `g` update in (4.36). -/
noncomputable def updateG {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin m → ℝ) (ε : ℝ) (f : Fin n → ℝ) (j : Fin m) : ℝ :=
  ε * Real.log (b j) -
    ε * Real.log (∑ i, gibbs C ε i j * Real.exp (f i / ε))

end CompOT.EntropicDual


