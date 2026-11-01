-- Prove2me | Definitions.Def_NoSignalPA_IsNonsignaling
-- name    : NoSignalPA_IsNonsignaling
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:03:29.242853+00:00
-- url     : https://prove2.me/theorems/5445f330-73a1-477b-bb54-cda4f6c290d5
-- title:
--   $(N_r+2)$-partite no signaling
-- statement:
--   A box $P_{\mathbf a,\mathbf b,e\mid\mathbf x,\mathbf y,z}$ is **$(N_r+2)$-partite nonsignaling** when no party can signal to the others: for each party, summing out its output leaves a quantity that does not depend on its input. The parties are Alice's $N_r$ systems, Bob (one system) and Eve (one system):
--
--   1. for each $i$, $\sum_{a_i\in\{0,1\}}P_{\mathbf a,\mathbf b,e\mid\mathbf x,\mathbf y,z}$ is unchanged when $x_i$ is replaced by any bit, all other inputs and outputs fixed;
--   2. $\sum_{\mathbf b}P_{\mathbf a,\mathbf b,e\mid\mathbf x,\mathbf y,z}$ does not depend on $\mathbf y$;
--   3. $\sum_{e}P_{\mathbf a,\mathbf b,e\mid\mathbf x,\mathbf y,z}$ does not depend on $z$.
--
--   No condition is imposed between the separate bits of Bob's string: Bob is a single "big" system, which is the weaker assumption the paper works with. The single-party conditions imply the corresponding conditions for every group of parties.
--
--   **Formalization Note** The equalities are between extended nonnegative reals; Eve's sum is an unconditional (`tsum`) sum.
-- source:
--   Masanes, Universally-composable privacy amplification from causality constraints, arXiv:0807.2158v4, pp.1–2 (No signaling, p.1; '(N + 2)-partite no signaling', p.2)

import Mathlib
import Definitions.Def_NoSignalPA_Box

namespace NoSignalPA

/-- **`(Nr + 2)`-partite no signaling.**
Ll. Masanes, *Universally-composable privacy amplification from causality constraints*,
arXiv:0807.2158v4, pp. 1–2: "We say that `P_{a,b|x,y}` is a nonsignaling distribution if the marginals depend
only on their corresponding observables" (p. 1), and "If the secret key is a function of Alice's
string k = h(a), then Bob's N systems can be considered as a single 'big' system ... We refer to
this assumption as '(N + 2)-partite no signaling'" (p. 2). Printed pp. 1–2 = PDF pp. 1–2.

The parties are Alice's `Nr` one-bit systems, Bob (one system) and Eve (one system). For each
party, summing out that party's output leaves a quantity that does not depend on that party's
input, all other inputs and outputs held fixed:

1. Alice's system `i`: `Σ_{a_i} P_{a,b,e|x,y,z}` does not change when `x_i` is replaced by any
   `c`;
2. Bob: `Σ_b P_{a,b,e|x,y,z}` does not depend on `y`;
3. Eve: `Σ_e P_{a,b,e|x,y,z}` does not depend on `z`.

**Formalization Note.** All equalities are in `ℝ≥0∞`, Eve's sum is a `tsum`. There is no
condition between separate bits of Bob's string: Bob is one party, as the paper says. The
single-party conditions imply the same for every subset of parties, by summing them in turn. -/
def IsNonsignaling.{u} {Nr : ℕ} {Z E : Type u} (P : Box Nr Z E) : Prop :=
  (∀ (i : Fin Nr) (x : Str Nr) (c : Bool) (y : Str Nr) (z : Z) (a b : Str Nr) (e : E),
      ∑ t : Bool, P x y z (Function.update a i t, b, e)
        = ∑ t : Bool, P (Function.update x i c) y z (Function.update a i t, b, e)) ∧
  (∀ (x y y' : Str Nr) (z : Z) (a : Str Nr) (e : E),
      ∑ b : Str Nr, P x y z (a, b, e) = ∑ b : Str Nr, P x y' z (a, b, e)) ∧
  (∀ (x y : Str Nr) (z z' : Z) (a b : Str Nr),
      ∑' e : E, P x y z (a, b, e) = ∑' e : E, P x y z' (a, b, e))

end NoSignalPA


