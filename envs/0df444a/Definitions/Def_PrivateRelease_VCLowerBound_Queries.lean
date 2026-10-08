-- Prove2me | Definitions.Def_PrivateRelease_VCLowerBound_Queries
-- name    : PrivateRelease_VCLowerBound_Queries
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T16:06:45.675336+00:00
-- url     : https://prove2.me/theorems/e700fd14-d515-4202-a5cc-3394531c1cfd
-- title:
--   Counting queries on input databases and (α, δ)-usefulness of a mechanism (Definitions 2.3, 2.10)
-- statement:
--   Let $X$ be a data universe and $n \ge 1$. An **input database** of size $n$ is a tuple $z = (z_1,\dots,z_n) \in X^n$; it is read as a multiset, so repeated entries count with multiplicity.
--
--   A **predicate** is a map $\varphi : X \to \{0,1\}$. Its **counting query** evaluated on $z$ is the fraction of entries that satisfy it:
--
--   $$Q_\varphi(z) = \frac{1}{n}\,\#\{\, i \in \{1,\dots,n\} : \varphi(z_i) = 1 \,\}.$$
--
--   A **mechanism** on databases of size $n$ assigns to each input $z$ a distribution $M(z)$ on an output space $O$. A **readout** $\mathrm{ans} : O \times \{\text{predicates}\} \to \mathbb R$ says which answer an output $o$ gives to the query $Q_\varphi$. For a class $C$ of predicates and $\alpha, \delta \in \mathbb R$, the mechanism is **$(\alpha,\delta)$-useful for $C$** if for every input $z \in X^n$
--
--   $$\Pr_{o \sim M(z)}\Big[\ \forall \varphi \in C:\ \big|\mathrm{ans}(o,\varphi) - Q_\varphi(z)\big| \le \alpha\ \Big] \ \ge\ 1 - \delta .$$
--
--   These are the objects in which the lower bound of Theorem 3.11 is stated: privacy and usefulness are properties of the same mechanism $M$.
--
--   **Formalization Note** Predicates are `X → Bool`. The paper's mechanisms output a synthetic database $\hat D$ and the readout is $\mathrm{ans}(\hat D,\varphi) = Q_\varphi(\hat D)$; the definition here allows an arbitrary output space and readout, which contains the paper's case (take $O$ to be the databases). A lower bound for this larger class of mechanisms is a stronger theorem. The probability of the event is the (outer) measure $M(z)$ gives it; it is a genuine probability whenever $C$ is countable and the readouts are measurable. On the empty input ($n = 0$) Lean's convention $x/0 = 0$ gives $Q_\varphi = 0$; every statement using this definition assumes $n \ge 1$.
-- source:
--   Blum, Ligett, Roth, A Learning Theory Approach to Non-Interactive Database Privacy, arXiv:1109.2229v1 (2011), pp. 6–7, Definitions 2.3, 2.10

import Mathlib

namespace PrivateRelease.VCLowerBound

open MeasureTheory

/-- Definition 2.3 (p. 6): the **counting query** `Q_φ` of a predicate `φ : X → {0,1}` evaluated on an
input database `z ∈ Xⁿ`, the fraction of its entries that satisfy `φ`:
`Q_φ(z) = (1/n) · #{i : φ(z_i) = 1}`. `Bool` stands for `{0,1}`. Entries are counted with
multiplicity (a database is a multiset). On the empty input (`n = 0`) Lean's `x / 0 = 0` gives `0`;
every statement that uses it assumes `1 ≤ n`. -/
noncomputable def countQ {X : Type} {n : ℕ} (φ : X → Bool) (z : Fin n → X) : ℝ :=
  ((Finset.univ.filter fun i => φ (z i) = true).card : ℝ) / n

/-- Definition 2.10 (p. 7): a mechanism `M` on input databases of size `n` is **(α, δ)-useful** for
the class `C` of counting queries if for every input `z ∈ Xⁿ`, with probability at least `1 − δ` the
output `o` answers every query of `C` within `α`: `|ans o φ − Q_φ(z)| ≤ α` for all `φ ∈ C`.

The output space `O` is arbitrary and `ans o φ` is the answer the output `o` gives to the query `φ`.
The paper's mechanisms output a synthetic database `D̂` and read off `ans D̂ φ = Q_φ(D̂)`; that is the
special case `O = ` databases, so this is a (weakly) more general notion. The measure of the event is
the outer measure `M z` assigns to it (the event is measurable whenever `C` is countable and each
`ans · φ` is measurable). -/
def IsUseful {X O : Type} [MeasurableSpace O] {n : ℕ} (C : Set (X → Bool)) (α δ : ℝ)
    (M : (Fin n → X) → Measure O) (ans : O → (X → Bool) → ℝ) : Prop :=
  ∀ z : Fin n → X, ENNReal.ofReal (1 - δ) ≤ M z {o | ∀ φ ∈ C, |ans o φ - countQ φ z| ≤ α}

end PrivateRelease.VCLowerBound


