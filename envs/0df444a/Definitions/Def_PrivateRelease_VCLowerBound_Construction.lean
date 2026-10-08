-- Prove2me | Definitions.Def_PrivateRelease_VCLowerBound_Construction
-- name    : PrivateRelease_VCLowerBound_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T16:06:52.166222+00:00
-- url     : https://prove2.me/theorems/27d94116-f960-412a-8e1a-7d1746275d37
-- title:
--   The family $\mathcal D_S$, the predicates $\varphi_T$, set databases and the reconstruction procedure (proof of Theorem 3.11, Lemma 3.13)
-- statement:
--   These are the objects of the proof of Theorem 3.11. Fix a finite set $S \subseteq X$ of universe elements and a size $m$.
--
--   1. The family of $m$-subsets of $S$: $$\mathcal D_S = \{\, T \subseteq S : |T| = m \,\}.$$ In the paper $|S| = d$ and $m = d/2$.
--   2. A predicate $\varphi$ **equals the indicator of $T$ on $S$** if, for every $x \in S$, $\varphi(x) = 1 \iff x \in T$. This is the predicate $\varphi_T$ that shattering of $S$ guarantees; its values outside $S$ are not constrained.
--   3. An input $z \in X^m$ **lists** a finite set $T$ if $z$ is injective and its entries are exactly the elements of $T$. This is how a set $T \in \mathcal D_S$ is fed to a mechanism as a database.
--   4. For a database given as a finite set $T$ of distinct elements, the counting query is $$Q_\varphi(T) = \frac{1}{|T|}\sum_{x \in T}\varphi(x).$$
--   5. The **reconstruction procedure**: given the predicates $(\varphi_{T'})_{T' \in \mathcal D_S}$, a readout $\mathrm{ans}$ and an output $o$, put $$v_{T'}(o) = Q_{\varphi_{T'}}(T') - \mathrm{ans}(o,\varphi_{T'})$$ and return a minimiser $T' \in \operatorname{argmin}_{T' \in \mathcal D_S} v_{T'}(o)$.
--
--   These objects let a sufficiently useful mechanism be turned into a reconstruction attack on databases drawn from $\mathcal D_S$ (Lemma 3.13).
--
--   **Formalization Note** Ties in the argmin are broken by a fixed but arbitrary choice (`Classical.choose`); Lemma 3.13 holds for every tie-breaking rule. If $\mathcal D_S$ is empty ($m > |S|$) the procedure returns $\emptyset$; the statements only use it with $|S| = 2m$. On $T = \emptyset$, $Q_\varphi(T) = 0$ by Lean's $x/0 = 0$.
-- source:
--   Blum, Ligett, Roth, A Learning Theory Approach to Non-Interactive Database Privacy, arXiv:1109.2229v1 (2011), p. 11, proof of Theorem 3.11 (D_S, φ_T, Q_T); pp. 11–12, proof of Lemma 3.13 (v_{T'}, argmin)

import Mathlib

namespace PrivateRelease.VCLowerBound

/-- Proof of Theorem 3.11 (p. 11): for a finite set `S ⊆ X` of universe elements and a size `m`, the
family `D_S = {T ⊆ S : |T| = m}`. In the paper `|S| = d` and `m = d/2`. -/
def DS {X : Type} (S : Finset X) (m : ℕ) : Finset (Finset X) :=
  S.powersetCard m

/-- Proof of Theorem 3.11 (p. 11): `φ` is a predicate that equals the indicator of `T` on `S`, i.e.
`φ(x) = 1` for `x ∈ T` and `φ(x) = 0` for `x ∈ S \ T` (the predicate `φ_T` "guaranteed by the
definition of shattering"; its values outside `S` are unconstrained). -/
def IsIndicatorOn {X : Type} (S T : Finset X) (φ : X → Bool) : Prop :=
  ∀ x ∈ S, (φ x = true ↔ x ∈ T)

/-- The input database `z ∈ X^m` lists the elements of the finite set `T`, each exactly once:
`z` is injective and its range is `T`. This is how a set `T ∈ D_S` is fed to a mechanism. -/
def IsEnum {X : Type} {m : ℕ} (T : Finset X) (z : Fin m → X) : Prop :=
  Function.Injective z ∧ ∀ x, x ∈ T ↔ ∃ i, z i = x

/-- Definition 2.3 (p. 6) for a database given as a finite set `T` of distinct elements (as in the
proof of Theorem 3.11, where databases are the sets `T ∈ D_S`): `Q_φ(T) = (Σ_{x∈T} φ(x)) / |T|`.
On `T = ∅` Lean's `x / 0 = 0` gives `0`. -/
noncomputable def countQF {X : Type} (φ : X → Bool) (T : Finset X) : ℝ :=
  ((T.filter fun x => φ x = true).card : ℝ) / T.card

/-- Proof of Lemma 3.13 (pp. 11–12): the **reconstruction procedure**. Given an output `o`, a readout
`ans`, and the family of predicates `φ_{T'}` (`T' ∈ D_S`), set
`v_{T'}(o) = Q_{T'}(T') − ans o φ_{T'}` and return a minimiser `T' = argmin_{T' ∈ D_S} v_{T'}(o)`.
Ties are broken by an arbitrary but fixed choice (`Classical.choose`); if `D_S` is empty (`m > |S|`)
it returns `∅`. -/
noncomputable def reconstruct {X O : Type} (S : Finset X) (m : ℕ) (φ : Finset X → X → Bool)
    (ans : O → (X → Bool) → ℝ) (o : O) : Finset X :=
  if h : (DS S m).Nonempty then
    Classical.choose
      (Finset.exists_min_image (DS S m) (fun T' => countQF (φ T') T' - ans o (φ T')) h)
  else ∅

end PrivateRelease.VCLowerBound


