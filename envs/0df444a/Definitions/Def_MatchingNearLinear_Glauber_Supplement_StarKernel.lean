-- Prove2me | Definitions.Def_MatchingNearLinear_Glauber_Supplement_StarKernel
-- name    : MatchingNearLinear_Glauber_Supplement_StarKernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:55:06.09004+00:00
-- url     : https://prove2.me/theorems/2533b3bc-b159-425e-ae5e-99fcf30afa19
-- title:
--   Variance and ordinary star Glauber dynamics
-- statement:
--   For a probability vector $p$ on a finite set and a real function $f$, $\operatorname{Var}_p(f)=\mathbb E_p[f^2]-(\mathbb E_pf)^2$.
--
--   Let $G$ be a labeled simple graph on $n$ vertices with base activities $\lambda$ and let $a>0$. **Star Glauber dynamics** $P^{G,a}_{\mathrm{star}}=n^{-1}\sum_v H_v$ acts on a matching $M$ as follows: choose a vertex $v$ uniformly among all $n$ vertices (isolated vertices included), erase the matching edge at $v$ if present, let
--   $$F_v(M)=\sum_{u\sim v,\ u\text{ unmatched after erasure}}\lambda_{uv},\qquad Z_v(M)=1+aF_v(M),$$
--   and leave $v$ unmatched with probability $1/Z_v(M)$ or match it to such a neighbour $u$ with probability $a\lambda_{uv}/Z_v(M)$. It is reversible with respect to $\mu_{G,a\lambda}$.
--
--   **Formalization Note** The kernel is written on all edge subsets; the law $\mu_{G,a\lambda}$ vanishes off matchings, so those rows do not enter any Dirichlet form.
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), §6, printed p. 28 (PDF p. 30); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_MatchingNearLinear_Glauber_Supplement_Peeling

set_option autoImplicit false

/-!
# Variance and ordinary star Glauber dynamics

Miao–Yin, *Sampling Matchings in Near-linear Time*, STOC 2027 submission #444, §6
(printed p. 28, PDF p. 30). From `M`, choose a vertex `v` uniformly among all `n` vertices,
erase the matching edge at `v` if present, put `F_v` the sum of the base weights `λ_{uv}` over
neighbours `u` that are unmatched after erasure and `Z_v = 1 + a F_v`; leave `v` unmatched with
probability `1/Z_v`, or match it to such a `u` with probability `a λ_{uv}/Z_v`.
-/

namespace MatchingNearLinear.Glauber.Supplement

open scoped BigOperators
noncomputable section
open Classical

open MatchingNearLinear.Glauber

/-- `Var_p(f) = E_p[f²] − (E_p f)²`. -/
def variance {α : Type} [Fintype α] (p f : α → ℝ) : ℝ :=
  mean p (fun x => (f x)^2) - (mean p f)^2

/-- Edge `e` is incident to vertex `v`. -/
def Incident {n m : ℕ} (G : Input n m) (e : Fin m) (v : Fin n) : Prop :=
  G.u e = v ∨ G.v e = v

/-- The endpoint of `e` other than `v` (for `e` incident to `v`). -/
def otherEnd {n m : ℕ} (G : Input n m) (e : Fin m) (v : Fin n) : Fin n :=
  if G.u e = v then G.v e else G.u e

/-- `M` with the matching edge at `v` erased. -/
def eraseAt {n m : ℕ} (G : Input n m) (M : Config m) (v : Fin n) : Config m :=
  M.filter fun e => ¬ Incident G e v

/-- Edges `uv` whose other endpoint `u` is unmatched after erasure. -/
def availableEdges {n m : ℕ} (G : Input n m) (M : Config m) (v : Fin n) : Finset (Fin m) :=
  Finset.univ.filter fun e => Incident G e v ∧ ¬ Covered G (eraseAt G M v) (otherEnd G e v)

/-- `Z_v(M) = 1 + a F_v(M)`, with `F_v` the sum of base weights over available neighbours. -/
def starNormalizer {n m : ℕ} (G : Input n m) (lam : Fin m → ℝ) (a : ℝ) (M : Config m)
    (v : Fin n) : ℝ :=
  1 + a * ∑ e ∈ availableEdges G M v, lam e

/-- The heat-bath update `H_v` of the star at `v`. -/
def starUpdate {n m : ℕ} (G : Input n m) (lam : Fin m → ℝ) (a : ℝ) (v : Fin n) :
    Matrix (Config m) (Config m) ℝ :=
  fun M M' =>
    (if M' = eraseAt G M v then 1 / starNormalizer G lam a M v else 0) +
    ∑ e ∈ availableEdges G M v,
      if M' = insert e (eraseAt G M v) then a * lam e / starNormalizer G lam a M v else 0

/-- Star Glauber dynamics `P_star^{G,a} = n⁻¹ Σ_v H_v`, a kernel for `μ_{G,aλ}`. -/
def starKernel {n m : ℕ} (G : Input n m) (lam : Fin m → ℝ) (a : ℝ) :
    Matrix (Config m) (Config m) ℝ :=
  fun M M' => (1 / (n : ℝ)) * ∑ v : Fin n, starUpdate G lam a v M M'

end

end MatchingNearLinear.Glauber.Supplement


