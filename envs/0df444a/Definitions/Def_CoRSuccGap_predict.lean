-- Prove2me | Definitions.Def_CoRSuccGap_predict
-- name    : CoRSuccGap_predict
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:48:21.99723+00:00
-- url     : https://prove2.me/theorems/09ef4d35-5c0e-4230-896f-f209b3f4677e
-- title:
--   Folds $\chi_\lambda$ at the hub, predictions $X^{(\lambda)}$, and compositions that notice a fold
-- statement:
--   Take the palette $\Lambda=2^{[k]}$ of subsets of $[k]=\{1,\dots,k\}$; the complement of a colour $\mu$ is $\mu^c=[k]\setminus\mu$. Fix a colouring $\chi$ of the pairs of distinct vertices of $V$ and a vertex $\hbar$, the **hub**. The **fold** of a colour $\lambda$ recolours every edge of colour $\lambda$ at the hub to $\lambda^c$: for $u\neq v$,
--
--   $$
--   \chi_\lambda(u,v):=\begin{cases}\lambda^c, & \hbar\in\{u,v\}\text{ and }\chi(u,v)=\lambda,\\ \chi(u,v), & \text{otherwise,}\end{cases}
--   $$
--
--   and every loop keeps the label $\mathbf{id}$. For a colour-determined relation $X$, its **prediction** reads the table of $X$ on the folded colouring:
--
--   $$
--   X^{(\lambda)}(u,v):=X[\chi_\lambda(u,v)]\qquad(u,v\in V).
--   $$
--
--   For colour-determined $X,Y$, the composition $X;Y$ **notices the fold of** $\lambda$ if $X^{(\lambda)};Y^{(\lambda)}\neq(X;Y)^{(\lambda)}$, an inequality of relations on $V$ that depends only on $X$, $Y$ and $\lambda$.
--
--   Folds and predictions turn the lower bound into counting: a circuit with no composition noticing the fold of $\lambda$ cannot distinguish the reference structure from its fold (Lemma 3.4), and each composition notices at most two folds (Lemma 3.5).
--
--   **Formalization Note** The palette $2^{[k]}$ is `Finset (Fin k)` with the Boolean-algebra complement; the colour $\lambda$ is the variable `lam`. `fold χ h lam` is $\chi_\lambda$ (its diagonal values are never read), `predict χ h lam X` is $X^{(\lambda)}$, with $X[\cdot]$ read by `tab`, and `NoticesComp χ h lam X Y` is noticing for composition. As in the paper, predictions are meant for colour-determined relations only.
-- source:
--   Y. Uezato, Y. Nakamura, An Exponential Succinctness Gap between Three-Variable Logic and the Calculus of Relations, arXiv:2609.26778 (held version, sha256 5ad6337daad55bcf6132960d4744d07ff7d67ef2a9aef456f3e3b54ff623c9b6), §3.2, p.19 (PDF 21) (palette, fold, prediction); §3.3, p.20 (PDF 22) (noticing); folded structure p.20 (PDF 22)

import Mathlib
import Definitions.Def_CoRSuccGap_ColorDet

set_option autoImplicit false

namespace CoRSuccGap

/-!
# Folds, predictions and noticing a fold

Uezato–Nakamura, *An Exponential Succinctness Gap between Three-Variable Logic and the
Calculus of Relations*, arXiv:2609.26778 (held version, sha256 5ad6337d…c9b6), §3.2, p.19 (PDF 21): "From now on, take the palette Λ := 2^[k] for some k ≥ 1 … The
complement of a color μ is the color μᶜ = [k] \ μ … The fold of a color λ recolors every edge of
color λ at the hub to λᶜ and leaves all other edges unchanged: for u ≠ v, χ_λ(u, v) := λᶜ if
ℏ ∈ {u, v} and χ(u, v) = λ, χ(u, v) otherwise, and every loop keeps the label id. … For a
color-determined relation X, its prediction X^(λ) reads the same values on χ_λ:
X^(λ)(u, v) := X[χ_λ(u, v)]." §3.3, p.20 (PDF 22): "we say that it notices the fold of λ at U if
op(U₁^(λ), …, U_r^(λ)) ≠ op(U)^(λ)."

**Formalization Note.**
* The palette 2^[k] is `Finset (Fin k)`, and μᶜ is the Boolean-algebra complement. The colour λ
  is the variable `lam` (`λ` is a Lean keyword).
* `fold χ h λ` is χ_λ with hub `h`; its diagonal values are never read (`lab` sends loops to id).
* `predict χ h λ X` is X^(λ)(u, v) = X[χ_λ(u, v)], with X[·] read by `tab`; it is meant for
  colour-determined `X` only, as in the paper.
* `NoticesComp χ h λ X Y` is noticing for op = composition: X^(λ); Y^(λ) ≠ (X; Y)^(λ), an
  inequality of whole relations determined by the operands `X, Y` on M₀.
-/

variable {V : Type*} [DecidableEq V] {k : ℕ}

/-- The fold χ_λ of the colour `λ` at the hub `h` (p.19): edges at `h` of colour `λ` get
colour `λᶜ`, all other edges keep their colour. -/
def fold (χ : Sym2 V → Finset (Fin k)) (h : V) (lam : Finset (Fin k)) :
    Sym2 V → Finset (Fin k) :=
  fun e => if h ∈ e ∧ χ e = lam then lamᶜ else χ e

/-- The prediction X^(λ)(u, v) := X[χ_λ(u, v)] (p.19). -/
def predict (χ : Sym2 V → Finset (Fin k)) (h : V) (lam : Finset (Fin k))
    (X : V → V → Prop) : V → V → Prop :=
  fun u v => tab χ X (lab (fold χ h lam) u v)

/-- The composition of `X` and `Y` notices the fold of `λ` (p.20):
X^(λ); Y^(λ) ≠ (X; Y)^(λ). -/
def NoticesComp (χ : Sym2 V → Finset (Fin k)) (h : V) (lam : Finset (Fin k))
    (X Y : V → V → Prop) : Prop :=
  (fun u v => ∃ w, predict χ h lam X u w ∧ predict χ h lam Y w v) ≠
    predict χ h lam (fun u v => ∃ w, X u w ∧ Y w v)

end CoRSuccGap


