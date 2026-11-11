-- Prove2me | Definitions.Def_JinMaoSubsetSum_CapOut
-- name    : JinMaoSubsetSum_CapOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:39:06.209201+00:00
-- url     : https://prove2.me/theorems/76c5663d-f074-4ec0-91d0-bcd951ffbc5a
-- title:
--   Rational bit lengths $\mathrm{maxbitlen}$, caps and enclosing parallelepipeds
-- statement:
--   For a rational $r=p/q$ in lowest terms, $\mathrm{maxbitlen}(r)=\max\{\log(2+|p|),\log(2+|q|)\}$ with $\log=\log_2$. It extends to vectors (maximum over coordinates), linear maps (over the coefficients), polytopes (over the vertices), multisets ($\max\{\log(2+|A|),\max_{a\in\operatorname{supp}A}\mathrm{maxbitlen}(a)\}$) and finite families (the maximum); a maximum over an empty set is $1$.
--
--   A **cap** of a convex set $K$ is $Q=K\cap\{x:\langle u,x\rangle\ge a\}$. Theorem 10.1 outputs caps $(u_i,a_i)$ together with enclosing parallelepipeds $P_i\supseteq Q_i$; a parallelepiped is $P=\{c+\sum_{j=1}^dt_je_j:|t_j|\le1\}$ with center $c$ and edge vectors $e_1,\dots,e_d$, and its vertices are $c+\sum_j\pm e_j$.
--
--   **Formalization Note** `mbl`, `mblVec`, `mblMs` are $\mathrm{maxbitlen}$ of a rational, a rational vector and a multiset of integer vectors; since every value is at least $1$, the empty-maximum convention is a `max 1`. `ParOut` is a parallelepiped with rational center and edges (`toSet` its points, `mbl` the maximum over its $2^d$ vertices), `CapOut` a cap with its parallelepiped (`capSet K` the cap of $K$, `mbl` the value $\mathrm{maxbitlen}(u_i,a_i,P_i)$). `CapOut.words` writes a cap as integers: each rational as numerator and denominator in lowest terms, in the order $u$, $a$, $c$, $e_1,\dots,e_d$.
-- source:
--   Jin, Mao, Subset Sum in Almost-Linear Time, arXiv:2610.20742v1 (sha256 8b604948862d9188e922b8abf95831fde3a3699e26d39177d20a1460e31a926a), §3.1, p.15 (PDF p.17); §6, p.30 (PDF p.32); Theorem 10.1, p.58 (PDF p.60)

import Mathlib
import Definitions.Def_JinMaoSubsetSum_zonotope

set_option autoImplicit false

namespace JinMaoSubsetSum

/-!
# Rational bit lengths, caps and enclosing parallelepipeds (the output of Theorem 10.1)

Jin, Mao, *Subset Sum in Almost-Linear Time*, arXiv:2610.20742v1, §3.1, p.15: "For r = p/q ∈ ℚ
in lowest terms, define maxbitlen(r) = max{log(2 + |p|), log(2 + |q|)}". §6, p.30: "For a
rational matrix M, define maxbitlen(M) = max_{i,j} maxbitlen(M_{i,j}); define maxbitlen(v) for a
rational vector v similarly. For a rational linear map f, let maxbitlen(f) = maxbitlen(M_f) [...].
For a rational polytope K, let maxbitlen(K) = max_v maxbitlen(v) where v ranges over its vertices.
[...] For a multiset A, define maxbitlen(A) = max{log(2 + |A|), max_{a∈supp(A)} maxbitlen(a)}. We
use the shorthand maxbitlen(x_1, . . . , x_k) = max_{1≤i≤k} maxbitlen(x_i). In these definitions, a
maximum over an empty set is taken to be 1." Theorem 10.1, p.58: "Caps Q_i = K ∩ {x : ⟨u_i, x⟩ ≥
a_i} with enclosing parallelepipeds P_i ⊇ Q_i".

**Formalization Note.**
* `log` is `log₂` (§3.1). `mbl r` uses Mathlib's lowest-terms `r.num`, `r.den`. Every
  `maxbitlen` is `≥ 1`, so the "maximum over an empty set is 1" convention is `max 1 (…)`.
* A parallelepiped is given by a center `c ∈ ℚ^d` and `d` edge vectors `e_1, …, e_d ∈ ℚ^d`:
  `P = {c + Σ_j t_j e_j : |t_j| ≤ 1}`; its vertices are `c + Σ_j ±e_j`, and `maxbitlen(P)` is the
  maximum over these `2^d` points.
* A cap `(u, a, P)` is the half-space `{x : ⟨u, x⟩ ≥ a}` (to be intersected with `K`) together
  with its enclosing parallelepiped `P`.
* Output words (`capWords`): every rational as the two integers `num, den` (lowest terms,
  `den > 0`), in the order `u` (coordinate `0` first), `a`, `c`, then `e_1, …, e_d`.
-/

/-- `maxbitlen(r) = max{log₂(2 + |p|), log₂(2 + |q|)}` for `r = p/q` in lowest terms. -/
noncomputable def mbl (r : ℚ) : ℝ :=
  max (Real.logb 2 (2 + |(r.num : ℝ)|)) (Real.logb 2 (2 + (r.den : ℝ)))

/-- `maxbitlen` of a rational vector: the maximum over its coordinates (`1` if there are none). -/
noncomputable def mblVec {d : ℕ} (v : Fin d → ℚ) : ℝ :=
  (List.ofFn (fun j => mbl (v j))).foldr max 1

/-- `maxbitlen` of a multiset of integer vectors: `max{log₂(2 + |X|), max_{x ∈ supp X} maxbitlen(x)}`. -/
noncomputable def mblMs {d : ℕ} (X : Multiset (Fin d → ℤ)) : ℝ :=
  max (Real.logb 2 (2 + (Multiset.card X : ℝ)))
    ((X.toFinset.toList.map (fun x => mblVec (fun j => ((x j : ℤ) : ℚ)))).foldr max 1)

/-- The cast of a rational vector to `ℝ^d`. -/
def qToR {d : ℕ} (v : Fin d → ℚ) : Fin d → ℝ := fun j => (v j : ℝ)

/-- A parallelepiped `{c + Σ_j t_j e_j : |t_j| ≤ 1}` with rational center and edges. -/
structure ParOut (d : ℕ) where
  center : Fin d → ℚ
  edge : Fin d → Fin d → ℚ

/-- The point set of a parallelepiped. -/
def ParOut.toSet {d : ℕ} (P : ParOut d) : Set (Fin d → ℝ) :=
  {x | ∃ t : Fin d → ℝ, (∀ j, |t j| ≤ 1) ∧ x = qToR P.center + ∑ j, t j • qToR (P.edge j)}

/-- The vertex `c + Σ_j σ_j e_j` (`σ_j = ±1`) of a parallelepiped. -/
def ParOut.vertex {d : ℕ} (P : ParOut d) (σ : Fin d → Bool) : Fin d → ℚ :=
  P.center + ∑ j, (if σ j then (1 : ℚ) else -1) • P.edge j

/-- `maxbitlen(P)`: the maximum of `maxbitlen` over the vertices of `P`. -/
noncomputable def ParOut.mbl {d : ℕ} (P : ParOut d) : ℝ :=
  ((Finset.univ : Finset (Fin d → Bool)).toList.map (fun σ => mblVec (P.vertex σ))).foldr max 1

/-- A cap `K ∩ {x : ⟨u, x⟩ ≥ a}` (normal `u`, offset `a`) with an enclosing parallelepiped. -/
structure CapOut (d : ℕ) where
  u : Fin d → ℚ
  a : ℚ
  par : ParOut d

/-- The cap `Q = K ∩ {x : ⟨u, x⟩ ≥ a}` of the convex set `K`. -/
def CapOut.capSet {d : ℕ} (Q : CapOut d) (K : Set (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  K ∩ {x | (Q.a : ℝ) ≤ ∑ j, (Q.u j : ℝ) * x j}

/-- `maxbitlen(u_i, a_i, P_i)`. -/
noncomputable def CapOut.mbl {d : ℕ} (Q : CapOut d) : ℝ :=
  max (mblVec Q.u) (max (JinMaoSubsetSum.mbl Q.a) Q.par.mbl)

/-- The two integer words `num, den` of a rational number. -/
def ratWords (r : ℚ) : List ℤ := [r.num, (r.den : ℤ)]

/-- The output words of a cap: `u`, `a`, the center, then the edges, each rational as `num, den`. -/
def CapOut.words {d : ℕ} (Q : CapOut d) : List ℤ :=
  (List.ofFn Q.u).flatMap ratWords ++ ratWords Q.a ++ (List.ofFn Q.par.center).flatMap ratWords ++
    (List.ofFn (fun j => (List.ofFn (Q.par.edge j)).flatMap ratWords)).flatten

end JinMaoSubsetSum


