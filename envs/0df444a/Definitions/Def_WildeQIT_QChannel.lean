-- Prove2me | Definitions.Def_WildeQIT_QChannel
-- name    : WildeQIT_QChannel
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T03:51:18.533889+00:00
-- url     : https://prove2.me/theorems/b4b58dfb-eb7f-434e-8891-e1e9e5b780c4
-- title:
--   Quantum channel in Choi–Kraus form: $\mathcal{N}(X) = \sum_l V_l X V_l^\dagger$, $\sum_l V_l^\dagger V_l = I$
-- statement:
--   **Definition 4.4.3 (Quantum Channel).** A quantum channel is a linear, completely positive, trace-preserving map $\mathcal{N} : \mathcal{L}(\mathcal{H}_A) \to \mathcal{L}(\mathcal{H}_B)$.
--
--   **Theorem 4.4.1 (Choi–Kraus).** A map $\mathcal{N} : \mathcal{L}(\mathcal{H}_A) \to \mathcal{L}(\mathcal{H}_B)$ is linear, completely positive, and trace-preserving if and only if it has a Choi–Kraus decomposition
--
--   $$
--   \mathcal{N}(X_A) = \sum_{l} V_l X_A V_l^\dagger, \qquad V_l \in \mathcal{L}(\mathcal{H}_A, \mathcal{H}_B), \qquad \sum_{l} V_l^\dagger V_l = I_A .
--   $$
--
--   By this theorem a quantum channel may be *represented* by a finite family of Kraus operators satisfying the completeness relation, and that is the representation adopted here. Channels are the objects whose distinguishability the diamond norm measures (Definition 9.1.3), and the trace distance is monotone under their action (Exercise 9.1.9).
--
--   **Formalization Note.** `WildeQIT.QChannel a b` is a structure bundling a finite index type `ι`, Kraus operators `K : ι → Matrix b a ℂ` (each a map $\mathcal{H}_A \to \mathcal{H}_B$), and the completeness relation `∑ i, (K i)ᴴ * K i = 1`. Its action on an input operator `X : Matrix a a ℂ` is `N.apply X = ∑ i, N.K i * X * (N.K i)ᴴ : Matrix b b ℂ`. Two Kraus families can represent the same map; statements about "a channel" quantify over the structure, so they hold for every Kraus representation.
-- source:
--   Wilde, *Quantum Information Theory*, 2nd ed. (Cambridge University Press, 2017; arXiv:1106.1445v8), §4.4.1 "Axiomatic Approach to Quantum Evolutions", Definition 4.4.3 (Quantum Channel) and Theorem 4.4.1 (Choi–Kraus).

import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic

/-!
Wilde, *Quantum Information Theory* (2nd ed.), §4.4.1, Definition 4.4.3 (Quantum Channel)
and Theorem 4.4.1 (Choi–Kraus).

Definition 4.4.3: "A quantum channel is a linear, completely positive, trace preserving map."

Theorem 4.4.1 (Choi–Kraus): a map `𝒩 : L(ℋ_A) → L(ℋ_B)` is linear, completely positive and
trace-preserving if and only if it has a Choi–Kraus decomposition
`𝒩(X_A) = ∑_l V_l X_A V_l†` with `V_l ∈ L(ℋ_A, ℋ_B)` and `∑_l V_l† V_l = I_A`.

We represent a quantum channel by such a Kraus decomposition.
-/

open Matrix

namespace WildeQIT

/-- **Quantum channel `𝒩 : L(ℋ_A) → L(ℋ_B)` in Choi–Kraus form** (Definition 4.4.3 via
Theorem 4.4.1): a finite family of Kraus operators `K i : Matrix b a ℂ` (maps `ℋ_A → ℋ_B`)
satisfying the completeness relation `∑ i, (K i)† (K i) = I_A`. -/
structure QChannel (a b : Type) [Fintype a] [Fintype b] [DecidableEq a] where
  /-- The index type of the Kraus family. -/
  ι : Type
  /-- The Kraus family is finite. -/
  [instFintype : Fintype ι]
  /-- The Kraus operators `V_l ∈ L(ℋ_A, ℋ_B)`. -/
  K : ι → Matrix b a ℂ
  /-- The completeness relation `∑_l V_l† V_l = I_A` (trace preservation). -/
  complete : ∑ i, (K i)ᴴ * K i = 1

attribute [instance] QChannel.instFintype

/-- **Action of the channel**: `𝒩(X) = ∑_l V_l X V_l†`. -/
def QChannel.apply {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    (N : QChannel a b) (X : Matrix a a ℂ) : Matrix b b ℂ :=
  ∑ i, N.K i * X * (N.K i)ᴴ

end WildeQIT


