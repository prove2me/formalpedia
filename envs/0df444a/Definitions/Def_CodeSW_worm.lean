-- Prove2me | Definitions.Def_CodeSW_worm
-- name    : CodeSW_worm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:25:38.889337+00:00
-- url     : https://prove2.me/theorems/4efc484f-4678-4b52-9dd8-0353be02e8bb
-- title:
--   Worm distribution $\omega_g$, worm space $\Omega_w$, its lifts $\phi^\uparrow,\phi^\downarrow$ and canonical paths through $\Omega_w$
-- statement:
--   Let $g\in\{0,1\}^{c\times m}$ be an edge-vertex incidence matrix. Write $\Omega_0=\ker(g^T)$ for the even subgraphs, and
--   $$\Omega_2:=\bigcup_{u<v}\Omega(u,v),\qquad\Omega(u,v)=\ker((g^T)_{[m]\setminus\{u,v\}})\setminus\Omega_0,$$
--   for the subgraphs with exactly two odd-degree vertices. The **worm space** is $\Omega_w=\Omega_0\cup\Omega_2$. With $w(S)=r^{|S|}$, the **worm distribution** is
--   $$\omega_g(S)\propto w(S)\mathbf 1(S\in\Omega_0)+\frac1{\binom m2}w(S)\mathbf 1(S\in\Omega_2).$$
--   The **primal lift** samples $S\sim\omega_g$ and adds each edge of $E\setminus S$ independently with probability $r$; $\phi^\uparrow$ is the law of the result. The **dual lift** does the same, and $\phi^\downarrow$ is the law of the complement of the result:
--   $$\phi^\uparrow(B)=\sum_{S\subseteq B}\omega_g(S)r^{|B\setminus S|}(1-r)^{|E\setminus B|},\qquad\phi^\downarrow(B)=\sum_{S\subseteq E\setminus B}\omega_g(S)r^{|(E\setminus B)\setminus S|}(1-r)^{|B|}.$$
--
--   A **set of canonical paths through $\Omega_w$** for the even cover law $\xi$ with cover space $L$ is a flow function $f$ with values in $[0,1]$ satisfying the following.
--
--   1. Every $\gamma$ with $f(\gamma)\ne0$ is a nonempty sequence moving by single-check flips $\gamma_{i+1}=\gamma_i\oplus e$, with endpoints in $L$ and interior states in $\Omega_w$.
--   2. For all $I\ne F$ in $L$, exactly one path from $I$ to $F$ carries weight, and that weight is $\xi(I)\xi(F)$.
--
--   **Formalization Note** The weight ratio $r=p_{\uparrow/\downarrow}/(1-p_{\uparrow/\downarrow})$ is a parameter, with $p_\uparrow=p/2$, $p_\downarrow=(1-p)/(2-p)$, so $r_\uparrow=p/(2-p)$ and $r_\downarrow=1-p$. The page's "we take $m\ge2$" holds for every incidence matrix with at least one row.
-- source:
--   Hangleiter, Ju, Vazirani, Code Swendsen-Wang Dynamics, arXiv:2510.08446 (manuscript sha256 4e4abb5e…), Definition 19, p.21; Definition 21, p.22; Definition 14, p.19; proof of Lemma 22, p.38

import Definitions.Def_CodeSW_kerA
import Definitions.Def_CodeSW_IsFlow
open Matrix
open scoped ENNReal
noncomputable section

namespace CodeSW

/-- `S ∈ Ω_0 = ker(gᵀ)`: the edge set `S` is an **even subgraph** of the graph with incidence
matrix `g` (Hangleiter, Ju, Vazirani, *Code Swendsen-Wang Dynamics*, arXiv:2510.08446, manuscript
sha256 4e4abb5e…, Definition 19, p.21). -/
def InOmega0 {c m : ℕ} (g : Matrix (Fin c) (Fin m) (ZMod 2)) (S : Finset (Fin c)) : Prop :=
  gᵀ *ᵥ ind S = 0

/-- `S ∈ Ω_2 = ⋃_{1 ≤ u < v ≤ m} Ω(u,v)` with `Ω(u,v) = ker((gᵀ)_{[m]∖{u,v}}) ∖ Ω_0`: the edge set
`S` has exactly two odd-degree vertices (arXiv:2510.08446, manuscript sha256 4e4abb5e…,
Definition 19, p.21).

**Formalization Note** `(gᵀ)_{[m]∖{u,v}}` is the row-submatrix of `gᵀ` without the rows `u, v`, so
`ind S ∈ ker((gᵀ)_{[m]∖{u,v}})` says `(gᵀ 1_S)_w = 0` for every vertex `w ∉ {u, v}`. -/
def InOmega2 {c m : ℕ} (g : Matrix (Fin c) (Fin m) (ZMod 2)) (S : Finset (Fin c)) : Prop :=
  (∃ u v : Fin m, u < v ∧ ∀ w : Fin m, w ≠ u → w ≠ v → (gᵀ *ᵥ ind S) w = 0) ∧ ¬ InOmega0 g S

/-- The **worm space** `Ω_w := Ω_0 ∪ Ω_2` (arXiv:2510.08446, manuscript sha256 4e4abb5e…,
Definition 19, p.21). -/
def InWormSpace {c m : ℕ} (g : Matrix (Fin c) (Fin m) (ZMod 2)) (S : Finset (Fin c)) : Prop :=
  InOmega0 g S ∨ InOmega2 g S

open Classical in
/-- The unnormalized worm weight `w(S) 1(S ∈ Ω_0) + (1/C(m,2)) w(S) 1(S ∈ Ω_2)` with
`w(S) = r^{|S|}` (arXiv:2510.08446, manuscript sha256 4e4abb5e…, Definition 19, p.21). -/
def wormWeight {c m : ℕ} (g : Matrix (Fin c) (Fin m) (ZMod 2)) (r : ℝ) (S : Finset (Fin c)) :
    ℝ :=
  r ^ S.card * (if InOmega0 g S then 1 else 0) +
    (1 / (m.choose 2 : ℝ)) * r ^ S.card * (if InOmega2 g S then 1 else 0)

/-- **Definition 19 (worm distribution).** `ω_g(S) ∝ w(S)1(S ∈ Ω_0) + (1/C(m,2)) w(S)1(S ∈ Ω_2)`,
`w(S) = (p↑/↓/(1 − p↑/↓))^{|S|}` (arXiv:2510.08446, manuscript sha256 4e4abb5e…, Definition 19,
p.21).

**Formalization Note** The weight ratio `r = p↑/↓/(1 − p↑/↓)` is the parameter: `r↑ = p/(2−p)`,
`r↓ = 1 − p` (pp.24, 36–38). The page's "we take `m ≥ 2`" holds for every incidence matrix with
at least one row; for `m < 2`, `Ω_2 = ∅` and `C(m,2) = 0` plays no role. -/
def worm {c m : ℕ} (g : Matrix (Fin c) (Fin m) (ZMod 2)) (r : ℝ) (S : Finset (Fin c)) : ℝ :=
  wormWeight g r S / ∑ T : Finset (Fin c), wormWeight g r T

/-- The **primal lift** `ϕ↑` of the worm distribution: sample `S ∼ ω_g` and add each edge
`e ∈ E ∖ S` independently with probability `r`; `ϕ↑(B) = ∑_{S ⊆ B} ω_g(S) r^{|B∖S|} (1−r)^{|E∖B|}`
(arXiv:2510.08446, manuscript sha256 4e4abb5e…, §3.3.2, p.21).

**Formalization Note** `r = p↑/(1 − p↑)`; `|E ∖ B| = c − |B|`. -/
def liftUp {c m : ℕ} (g : Matrix (Fin c) (Fin m) (ZMod 2)) (r : ℝ) (B : Finset (Fin c)) : ℝ :=
  ∑ S ∈ B.powerset, worm g r S * r ^ (B \ S).card * (1 - r) ^ (Finset.univ \ B).card

/-- The **dual lift** `ϕ↓` of the worm distribution: sample `S ∼ ω_g`, add each edge `e ∈ E ∖ S`
independently with probability `r` to obtain `B'`, and take the law of `E ∖ B'`;
`ϕ↓(B) = ∑_{S ⊆ E∖B} ω_g(S) r^{|(E∖B)∖S|} (1−r)^{|B|}` (arXiv:2510.08446, manuscript sha256
4e4abb5e…, §3.3.2, p.21).

**Formalization Note** `r = p↓/(1 − p↓)`. -/
def liftDown {c m : ℕ} (g : Matrix (Fin c) (Fin m) (ZMod 2)) (r : ℝ) (B : Finset (Fin c)) : ℝ :=
  ∑ S ∈ (Finset.univ \ B).powerset,
    worm g r S * r ^ ((Finset.univ \ B) \ S).card * (1 - r) ^ B.card

/-- **Definition 21 together with Definition 14 (canonical paths through the worm space).**
`f` is a set of canonical paths for the even-cover law `ξ` with cover space `L` through `Ω_w`:
1. `f` takes values in `[0, 1]`;
2. every path with `f(γ) ≠ 0` is nonempty, moves by single-check flips `γ_{i+1} = γ_i ⊕ e`,
   has endpoints `γ_0, γ_{L(γ)} ∈ L` and interior states `γ_i ∈ Ω_w`, `0 < i < L(γ)`;
3. for all `I ≠ F` in `L` exactly one path from `I` to `F` carries weight, and its weight is
   `ξ(I) ξ(F)`
(arXiv:2510.08446, manuscript sha256 4e4abb5e…, Definition 14, p.19; Definition 21, p.22;
proof of Lemma 22, p.38).

**Formalization Note** Subsets of checks are identified with their indicator vectors, so
`I ∈ L` is `1_I ∈ L`. The transitions of the worm-space paths are the single-check flips the
paper's paths use (`γ_{A,B} = (A, A ⊕ e_1, …, B)`, p.38). -/
def IsWormCanonicalPaths {c m : ℕ} (g : Matrix (Fin c) (Fin m) (ZMod 2))
    (L : Submodule (ZMod 2) (Fin c → ZMod 2)) (ξ : Finset (Fin c) → ℝ)
    (f : List (Finset (Fin c)) → ℝ≥0∞) : Prop :=
  (∀ γ, f γ ≤ 1) ∧
  (∀ γ, f γ ≠ 0 →
    γ ≠ [] ∧ List.IsChain (fun W W' => ∃ e : Fin c, W' = symmDiff W {e}) γ ∧
      (∀ I, γ.head? = some I → ind I ∈ L) ∧ (∀ F, γ.getLast? = some F → ind F ∈ L) ∧
      ∀ W ∈ γ.tail.dropLast, InWormSpace g W) ∧
  ∀ I F : Finset (Fin c), ind I ∈ L → ind F ∈ L → I ≠ F →
    ∃ γ₀ : List (Finset (Fin c)), γ₀.head? = some I ∧ γ₀.getLast? = some F ∧
      f γ₀ = ENNReal.ofReal (ξ I * ξ F) ∧
      ∀ γ, γ.head? = some I → γ.getLast? = some F → f γ ≠ 0 → γ = γ₀

end CodeSW


