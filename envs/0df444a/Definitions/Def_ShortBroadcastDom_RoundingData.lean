-- Prove2me | Definitions.Def_ShortBroadcastDom_RoundingData
-- name    : ShortBroadcastDom_RoundingData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:39.718926+00:00
-- url     : https://prove2.me/theorems/3e3085e2-35b3-441f-93cb-a196cd90e917
-- title:
--   The threshold rounding rule of §7.1: $W$, $R$, $h$, $H$, $U$, $D=W\cup H\cup U$ and $O$, $L$, $w$, $\ell$, $P$
-- statement:
--   Fix $a\ge 1$ and put $b=2a+1$ and $t=1/(a+1)$. Let $C\subseteq V(G)$ be a candidate set, $R_0\subseteq C$ a set of demands, $0<c(v)\le b$ costs on $C$, and $x\in[0,1]^C$ a feasible fractional cover of $R_0$, i.e. $\sum_{v\in N_G[r]\cap C}x_v\ge 1$ for $r\in R_0$. Write $\mathcal C(x)=\sum_{v\in C}c(v)x_v$. The rule is:
--
--   1. Step 1: $W=\{v\in C: c(v)=b,\ x_v>t\}$ and $R=R_0\setminus N_G[W]$;
--   2. Step 2: $h(v)=|N_G[v]\cap R|$ for $v\in C\setminus W$ and $H=\{v\in C\setminus W: h(v)\ge b\}$;
--   3. Step 3: $U=R\setminus N_G[H]$, and the output is $D=W\cup H\cup U$.
--
--   For the analysis, $O=C\setminus(W\cup H)$, $L=R\setminus(H\cup U)$, $w=|W|$, $\ell=|L|$ and
--
--   $$
--   P=\sum_{v\in O}(c(v)-h(v))\,x_v.
--   $$
--
--   Two instances are used: the integer case of §7.2 ($C=V(G)\setminus F$ with the costs of the first selection, $a=d/2$) and the non-integer case of §7.3 ($C=R_0=V(G)$ and constant costs $b$).
--
--   **Formalization Note** The data $(a,C,R_0,c,x)$ form a structure, and each set is a function of it and of $G$; the conditions above (including $a\ge1$, $R_0\subseteq C$ and the cost bounds) are the separate predicate `IsRoundingSetting`, and feasibility of $x$ on $C$ is `IsFeasibleOn`. Values of $x$ and $c$ outside $C$ are never read.
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), §7.1, pp.43–44 (PDF pp.46–47); §7.3, p.47 (PDF p.50)

import Mathlib
import Definitions.Def_ShortBroadcastDom_closedNbhd

namespace ShortBroadcastDom

/-- **The data of the threshold rounding rule of §7.1**: the density parameter `a`, a candidate
set `C`, a demand set `R₀`, costs `c` and a fractional vector `x`.

Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), §7.1, p.43 (PDF 46): "Fix a ≥ 1, and put b = 2a + 1 and t = 1/(a + 1). Let C ⊆ V(G) be
a candidate set, with demands R0 ⊆ C, costs 0 < c(v) ≤ b, and a feasible fractional cover
x ∈ [0, 1]^C of R0." The conditions on these data are `IsRoundingSetting`; the sets of the rule
are the functions below. -/
structure RoundingData (V : Type) where
  /-- The density parameter `a ≥ 1`. -/
  a : ℝ
  /-- The candidate set `C`. -/
  C : Finset V
  /-- The demand set `R₀`. -/
  R0 : Finset V
  /-- The costs `c(v)`. -/
  c : V → ℝ
  /-- The fractional vector `x` (only its values on `C` are used). -/
  x : V → ℝ

namespace RoundingData

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (d : RoundingData V)

/-- `b = 2a + 1`. -/
noncomputable def b : ℝ := 2 * d.a + 1

/-- The threshold `t = 1/(a + 1)`. -/
noncomputable def t : ℝ := 1 / (d.a + 1)

/-- The cost `𝒞(x) = ∑_{v ∈ C} c(v) x_v` of the fractional cover. -/
noncomputable def cost : ℝ := ∑ v ∈ d.C, d.c v * d.x v

open Classical in
/-- Step 1: `W = {v ∈ C : c(v) = b, x_v > t}`. -/
noncomputable def W : Finset V := d.C.filter fun v => d.c v = d.b ∧ d.t < d.x v

open Classical in
/-- The demands still uncovered after Step 1: `R = R₀ \ N_G[W]`. -/
noncomputable def R : Finset V := d.R0.filter fun r => ∀ w ∈ d.W, r ∉ closedNbhd G w

/-- `h(v) = |N_G[v] ∩ R|`, the number of remaining demands that `v` covers. -/
noncomputable def h (v : V) : ℕ := (closedNbhd G v ∩ d.R G).card

open Classical in
/-- Step 2: `H = {v ∈ C \ W : h(v) ≥ b}`. -/
noncomputable def H : Finset V := (d.C \ d.W).filter fun v => d.b ≤ (d.h G v : ℝ)

open Classical in
/-- Step 3: `U = R \ N_G[H]`, the demands still uncovered, all selected. -/
noncomputable def U : Finset V := (d.R G).filter fun r => ∀ v ∈ d.H G, r ∉ closedNbhd G v

/-- The returned set `D = W ∪ H ∪ U`. -/
noncomputable def D : Finset V := d.W ∪ d.H G ∪ d.U G

/-- `O = C \ (W ∪ H)`, the candidates not selected in Steps 1 and 2. -/
noncomputable def O : Finset V := d.C \ (d.W ∪ d.H G)

/-- `L = R \ (H ∪ U)`, the demands covered by `H` but not selected into `H`. -/
noncomputable def L : Finset V := d.R G \ (d.H G ∪ d.U G)

/-- `w = |W|`. -/
noncomputable def wCard : ℕ := d.W.card

/-- `ℓ = |L|`. -/
noncomputable def ell : ℕ := (d.L G).card

/-- `P = ∑_{v ∈ O} (c(v) − h(v)) x_v`. -/
noncomputable def P : ℝ := ∑ v ∈ d.O G, (d.c v - (d.h G v : ℝ)) * d.x v

end RoundingData

/-- `IsFeasibleOn G C R₀ x`: `x ∈ [0, 1]^C` is a feasible fractional cover of `R₀` using only
candidates in `C`, i.e. `∑_{v ∈ N_G[r] ∩ C} x_v ≥ 1` for every `r ∈ R₀` (§7.1, p.44, proof of (20):
"its constraint ∑_{v ∈ N_G[u] ∩ C} x_v ≥ 1"). Values of `x` outside `C` are irrelevant. -/
def IsFeasibleOn {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (C R0 : Finset V) (x : V → ℝ) : Prop :=
  (∀ v ∈ C, 0 ≤ x v ∧ x v ≤ 1) ∧ ∀ r ∈ R0, 1 ≤ ∑ v ∈ closedNbhd G r ∩ C, x v

/-- **The setting of the rounding rule** (§7.1, p.43, PDF 46): `a ≥ 1`, `R₀ ⊆ C`,
`0 < c(v) ≤ b` on `C`, and `x ∈ [0, 1]^C` a feasible fractional cover of `R₀` by `C`.

**Formalization Note** The costs are only constrained on `C`; nothing outside `C` enters the rule. -/
def IsRoundingSetting {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (d : RoundingData V) : Prop :=
  1 ≤ d.a ∧ d.R0 ⊆ d.C ∧ (∀ v ∈ d.C, 0 < d.c v ∧ d.c v ≤ d.b) ∧ IsFeasibleOn G d.C d.R0 d.x

/-- The rounding data of the non-integer case, §7.3, p.47 (PDF 50): "Apply Lemma 7.1 with
C = R0 = V(G) and the constant costs c(v) = b", with `b = 2a + 1`. -/
noncomputable def uniformRounding {V : Type} [Fintype V] (a : ℝ) (x : V → ℝ) : RoundingData V where
  a := a
  C := Finset.univ
  R0 := Finset.univ
  c := fun _ => 2 * a + 1
  x := x

end ShortBroadcastDom


