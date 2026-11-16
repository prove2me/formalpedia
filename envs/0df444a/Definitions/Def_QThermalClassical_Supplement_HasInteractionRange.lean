-- Prove2me | Definitions.Def_QThermalClassical_Supplement_HasInteractionRange
-- name    : QThermalClassical_Supplement_HasInteractionRange
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:35:52.447892+00:00
-- url     : https://prove2.me/theorems/d578d56f-49d9-4f9c-8b51-6b9af2679dfa
-- title:
--   Interaction range $R$ and the distance $d(X,Y)$
-- statement:
--   Let the qubits form a finite metric space $(\Lambda,d)$. A Pauli Hamiltonian $H=\sum_Pc_PP$ has **interaction range** $R$ (is geometrically local with range $R$) if every term has support of diameter at most $R$:
--   $$
--   \max_{x,y\in\mathrm{supp}\,P}d(x,y)\le R\qquad\text{for every } P \text{ with } c_P\neq0 .
--   $$
--   For finite sets $X,Y\subseteq\Lambda$, $d(X,Y)=\min_{x\in X,\,y\in Y}d(x,y)$.
--
--   **Formalization Note** The paper's sites are a lattice $\Lambda\subset\mathbb Z^D$ with Euclidean distance; here any finite metric space. For empty $X$ or $Y$ (where the paper's $d(X,Y)$ is undefined) the value is $0$.
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 5, eq. (40), p.17; §5.4, eq. (279), p.58

import Mathlib
import Definitions.Def_QThermalClassical_pauliOp

set_option autoImplicit false

namespace QThermalClassical.Supplement

/-- `H = Σ_P c_P P` on a metric space of sites `Λ` is geometrically local with interaction range
`R` (eqs. (40), (279)): every term (word with `c P ≠ 0`) has support of diameter at most `R`,
`max_{x,y ∈ supp P} d(x, y) ≤ R`.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 5, eq. (40), p.17, and §5.4, eq. (279), p.58.

**Formalization Note.** The sites are any finite metric space; the paper's `Λ ⊂ ℤ^D` with the
Euclidean distance is the instance used in §5.4. -/
def HasInteractionRange {Λ : Type} [Fintype Λ] [MetricSpace Λ] (R : ℝ)
    (c : PauliWord Λ → ℝ) : Prop :=
  ∀ P : PauliWord Λ, c P ≠ 0 → ∀ x ∈ pauliSupport P, ∀ y ∈ pauliSupport P, dist x y ≤ R

/-- The distance of two finite site sets, `d(X, Y) = min_{x∈X, y∈Y} d(x, y)` (§5.4, p.58).

**Formalization Note.** For nonempty `X, Y` this is the attained minimum; if `X` or `Y` is
empty the real `sInf ∅ = 0` is used (the paper leaves `d(∅, ·)` undefined; an observable
supported on `∅` is a scalar and has zero covariance with everything). -/
noncomputable def setDist {Λ : Type} [MetricSpace Λ] (X Y : Finset Λ) : ℝ :=
  sInf ((fun p : Λ × Λ => dist p.1 p.2) '' ((X ×ˢ Y : Finset (Λ × Λ)) : Set (Λ × Λ)))

end QThermalClassical.Supplement


