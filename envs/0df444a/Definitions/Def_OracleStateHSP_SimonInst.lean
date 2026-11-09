-- Prove2me | Definitions.Def_OracleStateHSP_SimonInst
-- name    : OracleStateHSP_SimonInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:31:42.316203+00:00
-- url     : https://prove2.me/theorems/a57e674e-8925-40aa-8056-03c9d83af18e
-- title:
--   Instance set $X_m$: Simon functions with nonzero period
-- statement:
--   $X_m$ is the set of Simon functions $f : \mathbb Z_2^m \to \mathbb Z_2^m$ with a **nonzero** hidden period $s(f)$, and $s : X_m \to \mathbb Z_2^m \setminus \{0\}$ returns that period. This is the instance set of Proposition 4.7, Lemma 4.9 and the proof of Theorem 4.10.
--
--   **Formalization Note** An element is a pair $(f, s)$ with $f$ hiding $s$ and $s \ne 0$. A nonzero period is unique (the unique nonzero $x$ with $f(x) = f(0)$), so the pairs are in bijection with the functions.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, proof of Theorem 4.10, p.40; Proposition 4.7, p.37

import Mathlib
import Definitions.Def_OracleStateHSP_IsSimonFn

namespace OracleStateHSP

/-- The instance set `X` of the proof of Theorem 4.10 (Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, p.40; also Proposition 4.7 and
Lemma 4.9, pp.37–38): the Simon functions on `Z_2^m` with **nonzero** hidden period, each listed
with its period, so that the answer function `s : X → Z_2^m \ {0}` is the second component.

**Formalization Note.** An element is a pair `(f, s)` with `IsSimonFn f s` and `s ≠ 0`. A nonzero
period of `f` is unique (it is the unique nonzero `x` with `f x = f 0`), so the pairs are in
bijection with the paper's set of functions. -/
def SimonInst (m : ℕ) : Type :=
  {p : (V m → V m) × V m // IsSimonFn p.1 p.2 ∧ p.2 ≠ 0}

noncomputable instance (m : ℕ) : Fintype (SimonInst m) := by
  unfold SimonInst; infer_instance

instance (m : ℕ) : DecidableEq (SimonInst m) := by
  unfold SimonInst; infer_instance

/-- The Simon function `f` of an instance. -/
def SimonInst.fn {m : ℕ} (x : SimonInst m) : V m → V m := x.1.1

/-- The (nonzero) hidden period `s(f)` of an instance. -/
def SimonInst.period {m : ℕ} (x : SimonInst m) : V m := x.1.2

end OracleStateHSP


