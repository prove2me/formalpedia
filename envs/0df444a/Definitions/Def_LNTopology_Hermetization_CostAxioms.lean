-- Prove2me | Definitions.Def_LNTopology_Hermetization_CostAxioms
-- name    : LNTopology_Hermetization_CostAxioms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:16:28.895922+00:00
-- url     : https://prove2.me/theorems/8df75969-8159-4d1e-8611-a100856d14c5
-- title:
--   Cost axioms (MO), (SY), (CI), (SA), (SA+) (corrected)
-- statement:
--   A channel cost function $c:\mathbb R\to\mathbb R$ together with a function $g_+$ (written $g$) satisfies the **cost axioms** when:
--
--   1. (MO) monotonicity: $c(x)>c(y)$ for $x>y\ge 0$;
--   2. (SY) symmetry: $c(-x)=c(x)$;
--   3. (CI) costless inaction: $c(0)=0$;
--   4. (SA) subadditivity: $c(x+y)<c(x)+c(y)$ for $x>y>0$;
--   5. $g_+$ is strictly increasing on $\mathbb R_+=[0,\infty)$;
--   6. (SA+) for every natural number $k\ge 1$ and every $x>0$,
--   $$c(kx)<\frac{k}{g_+(k)}\,c(x).$$
--
--   (SA+) quantifies "if the flow in a channel grows $k$-fold, the relative savings grow": the cost of a $k$-fold flow is at most a $1/g_+(k)$ fraction of $k$ separate channels. Every theorem of the mission assumes these axioms.
--
--   **Formalization Note** Two printed axioms are unsatisfiable as printed and are corrected minimally. The page states (SA+) as $c(kx)<\frac{k}{g_+(k)}c(x)$, $k\in\mathbb R_+$, with $x$ unrestricted: at $x=0$ it reads $0<0$ by (CI). Here $x>0$ is required, and $k$ ranges over the natural numbers $k\ge1$, the only values the paper's proofs use ($k=d(i)$); requiring it for fewer $k$ is a weaker assumption. The page states (SA) for $x>y\ge0$: at $y=0$ it reads $c(x)<c(x)$. Here $y>0$ is required. The codomain $\mathbb R_+$ of $c$ is not a separate axiom, since $c(x)=c(|x|)\ge c(0)=0$ follows from (MO), (SY), (CI); positivity of $g_+(k)$ for $k\ge1$ follows from (SA+). The function $c(x)=\sqrt{|x|}$ with $g_+(k)=\sqrt k/2$ satisfies all six axioms.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), §2.2, axioms (MO), (SY), (CI), (SA), (SA+), p. 5 (PDF p. 6)

import Mathlib

namespace LNTopology.Hermetization

/-- **The cost axioms (MO)–(SA+).**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), §2.2, axioms (MO), (SY), (CI), (SA), (SA+), p. 5.

The channel cost `c : ℝ → ℝ` and the function `g` (the paper's `g₊`) satisfy:
* (MO) `c x > c y` for `x > y ≥ 0`;
* (SY) `c (-x) = c x`;
* (CI) `c 0 = 0`;
* (SA) `c (x + y) < c x + c y` for `x > y > 0` (corrected, see below);
* `g` is strictly increasing on `ℝ₊ = [0, ∞)`;
* (SA+) `c (k x) < (k / g k) c x` for every natural `k ≥ 1` and every `x > 0` (corrected).

**Formalization Note.**
* Correction C1. The page prints (SA+) as "c(kx) < k/g₊(k) c(x), k ∈ R+" with `x` unrestricted.
  At `x = 0` this reads `0 < 0` by (CI), so the printed axioms are unsatisfiable. The Lean
  axiom requires `x > 0` (negative `x` adds nothing, by (SY)) and asks it only for natural
  `k ≥ 1`, the only values the paper's proof uses (`k = d(i)`); asking it for fewer `k` is a
  weaker hypothesis. `k = 1` is kept: it forces `g 1 < 1`.
* Correction C4. The page prints (SA) for `x > y ≥ 0`; at `y = 0` it reads
  `c x < c x + c 0 = c x`, unsatisfiable. The Lean axiom asks it for `y > 0`. (SA) is not used
  by the paper's proofs of Theorem 3.8 and Lemmas B.1–B.4, but it is printed and is kept.
* The codomain `ℝ₊` of `c` is not a field: `c x = c |x| ≥ c 0 = 0` follows from (MO), (SY),
  (CI). The codomain `ℝ₊` of `g` is not a field: (SA+) forces `g k > 0` for natural `k ≥ 1`
  (if `g k ≤ 0`, then `k / g k * c x ≤ 0 ≤ c (k x)`; Lean's `k / 0 = 0` is covered).
* `g` is defined on all of `ℝ`; only its values on `[0, ∞)` matter. -/
structure CostAxioms (c g : ℝ → ℝ) : Prop where
  /-- (MO) monotonicity: `c x > c y` for `x > y ≥ 0`. -/
  mono : ∀ x y : ℝ, 0 ≤ y → y < x → c y < c x
  /-- (SY) symmetry. -/
  symm : ∀ x : ℝ, c (-x) = c x
  /-- (CI) costless inaction. -/
  zero : c 0 = 0
  /-- (SA) subadditivity, for `x > y > 0` (correction C4). -/
  subadd : ∀ x y : ℝ, 0 < y → y < x → c (x + y) < c x + c y
  /-- `g₊` is strictly increasing on `ℝ₊ = [0, ∞)`. -/
  g_strictMonoOn : StrictMonoOn g (Set.Ici 0)
  /-- (SA+) for natural `k ≥ 1` and `x > 0` (correction C1). -/
  subadd_plus : ∀ k : ℕ, 1 ≤ k → ∀ x : ℝ, 0 < x → c (k * x) < k / g k * c x

end LNTopology.Hermetization


