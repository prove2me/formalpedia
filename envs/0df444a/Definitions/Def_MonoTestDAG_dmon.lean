-- Prove2me | Definitions.Def_MonoTestDAG_dmon
-- name    : MonoTestDAG_dmon
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:08:35.516924+00:00
-- url     : https://prove2.me/theorems/53e6ea74-d2b5-4522-94a8-15b3d1a98197
-- title:
--   Monotone functions, the distance $d_{\mathrm{mon}}$ and $\varepsilon$-farness
-- statement:
--   Let $G=(V,E)$ be a directed graph with $n=|V|$. A function $f:V\to\mathbb R$ is **monotone** if $f(u)\le f(v)$ whenever $u\leadsto v$. Its **distance to monotonicity** is
--   $$
--   d_{\mathrm{mon}}(f):=\min_{g:V\to\mathbb R\ \text{monotone}}\bigl|\{v\in V: f(v)\ne g(v)\}\bigr|.
--   $$
--   For $\varepsilon>0$, the function $f$ is **$\varepsilon$-far** from monotonicity if $d_{\mathrm{mon}}(f)>\varepsilon n$ (a strict inequality). The **violation relation** is $u\prec_f v$ iff $u\leadsto v$ and $f(u)>f(v)$.
--
--   These are the objects a monotonicity tester distinguishes: monotone functions from $\varepsilon$-far ones.
--
--   **Formalization Note.** The minimum is the infimum of a set of natural numbers. The set is nonempty because constant functions are monotone, so the infimum is attained and no default value occurs. The module also defines `IsMonotone`, `IsFar` and `Violates`.
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), §2.3, pp.10–11

import Mathlib
import Definitions.Def_MonoTestDAG_Reach

namespace MonoTestDAG

/-- `f : V → ℝ` is monotone (order-preserving): `f u ≤ f v` whenever `u ⇝ v`.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), §1.1, p.1 and §2.3, p.10. -/
def IsMonotone {V : Type} (E : V → V → Prop) (f : V → ℝ) : Prop :=
  ∀ u v, Reach E u v → f u ≤ f v

open Classical in
/-- The distance to monotonicity `d_mon(f) = min_{g monotone} |{v ∈ V : f(v) ≠ g(v)}|`.

Yoshida, arXiv:2602.15341 (sha256 454609db…), §2.3, p.10.

**Formalization Note.** The minimum is `sInf` of the set of attained Hamming distances; the set is
nonempty (constant functions are monotone), so `sInf` is the minimum, with no junk value. -/
noncomputable def dmon {V : Type} [Fintype V] (E : V → V → Prop) (f : V → ℝ) : ℕ :=
  sInf {k | ∃ g : V → ℝ, IsMonotone E g ∧ (Finset.univ.filter (fun v => f v ≠ g v)).card = k}

/-- `f` is `ε`-far from monotonicity: `d_mon(f) > ε n` with `n = |V|` (strict inequality).
Yoshida, arXiv:2602.15341 (sha256 454609db…), §2.3, p.11. -/
def IsFar {V : Type} [Fintype V] (E : V → V → Prop) (ε : ℝ) (f : V → ℝ) : Prop :=
  ε * (Fintype.card V : ℝ) < (dmon E f : ℝ)

/-- The violation relation `u ≺_f v`: `u ⇝ v` and `f(u) > f(v)` (a violating pair, or the
diagonal-free edge `{u_L, v_R}` of the violation graph `G_f`).
Yoshida, arXiv:2602.15341 (sha256 454609db…), §2.3, p.11. -/
def Violates {V : Type} (E : V → V → Prop) (f : V → ℝ) (u v : V) : Prop :=
  Reach E u v ∧ f v < f u

end MonoTestDAG


