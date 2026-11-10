-- Prove2me | Definitions.Def_SuperlatSVP_lat
-- name    : SuperlatSVP_lat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:44:22.592833+00:00
-- url     : https://prove2.me/theorems/0cf36577-9cfe-4421-a3c4-e4840b8e18ec
-- title:
--   Lattices $L(B)=B\mathbb Z^n$, the minimum $\lambda_1$, point counts $N_L(R)$, the bound (2.3), Gaussian masses $\rho_s(S)$ and $Z_\sigma(L)$
-- statement:
--   Let $B=(b_1,\dots,b_n)$ be an $n\times n$ real matrix with columns $b_j$. The **lattice** spanned by $B$ is
--   $$L(B)=B\mathbb Z^n=\Big\{\sum_j k_j b_j : k\in\mathbb Z^n\Big\}\subset\mathbb R^n .$$
--   It is full rank, with basis $B$, exactly when $\det B\ne0$, and then $\det L=|\det B|$. The paper considers only full-rank lattices.
--
--   For a lattice $L$:
--
--   1. the **minimum** $\lambda_1(L)$ is the length of a shortest nonzero vector, $\lambda_1(L)=\min_{v\in L\setminus\{0\}}\|v\|$;
--   2. the **point count** is $N_L(R)=|\{v\in L\setminus\{0\}:\|v\|\le R\}|$. Appendix A writes $C_L(T)=N_L(\sqrt T)$;
--   3. the **point-count bound (2.3)** with exponent $\beta$ and prefactor $A_n$ says that, with $b=2^\beta$,
--   $$N_L(r\,\lambda_1(L))\le A_n\,b^n r^n\qquad(r\ge1);$$
--   4. for $s>0$ and a discrete set $S\subset\mathbb R^n$, the **Gaussian mass** is $\rho_s(S)=\sum_{x\in S}\rho_s(x)$, where $\rho_s(x)=e^{-\pi\|x\|^2/s^2}$;
--   5. Appendix A uses the variance-type sum $Z_\sigma(L)=\sum_{v\in L}e^{-\|v\|^2/(2\sigma^2)}$. It is related to $\rho_s$ by $s=\sqrt{2\pi}\,\sigma$.
--
--   These are the objects of every statement in the mission.
--
--   **Formalization Note** $\lambda_1$ is an infimum over the lengths of nonzero lattice vectors. For full-rank $L$ with $n\ge1$ it is attained, and for $n=0$ it is $0$. $N_L$ is an extended natural number (`Set.encard`), so an infinite set does not count as $0$. The masses are sums of nonnegative terms in $[0,\infty]$, and they are finite for lattices. $\rho_s$ is the published `RegevLWE.GaussConv.rho`. In (2.3), $b^n$ is written $2^{\beta n}$ and $A$ is a sequence evaluated at the dimension.
-- source:
--   Hhan, Kim, Kim, Laarhoven, Superlattice methods for the shortest vector problem and discrete Gaussian sampling, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §2.1, p.14 (PDF p.14), (2.3); §2.2, p.16; Appendix A, (A.1)–(A.2), p.87, (A.35), p.91

import Mathlib
import Definitions.Def_RegevLWE_GaussConv_Gaussian

open MeasureTheory
open scoped ENNReal

namespace SuperlatSVP

/-- The ambient space `ℝⁿ` with its Euclidean norm and Lebesgue measure. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A coordinate vector `v : Fin n → ℝ` viewed as a point of `ℝⁿ`. -/
abbrev vecE {n : ℕ} (v : Fin n → ℝ) : E n := WithLp.toLp 2 v

/-- The lattice `L(B) = Bℤⁿ` spanned by the columns `b_j` of the `n × n` real matrix `B`.
Hhan, Kim, Kim, Laarhoven, *Superlattice methods for the shortest vector problem and discrete
Gaussian sampling*, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §2.1, p.14 (PDF p.14):
"An n-dimensional lattice L ⊂ ℝⁿ consists of the integer linear combinations of a basis
B = (b1, . . . , bn). We write L = L(B) = BZⁿ. All lattices considered here have full rank in their
ambient space. The determinant of L is det L = |det B|."

**Formalization Note.** A lattice is the `ℤ`-span of the columns; it is full rank (and the columns
are a basis) exactly when `B.det ≠ 0`, which every statement assumes explicitly. `det L` is
`|B.det|`. -/
noncomputable def lat {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : Submodule ℤ (E n) :=
  Submodule.span ℤ (Set.range fun j : Fin n => vecE (fun i => B i j))

/-- `λ₁(L)`, the length of a shortest nonzero vector (§2.1, p.14; (A.1), p.87).

**Formalization Note.** Written as an infimum of the lengths of nonzero lattice vectors. For a
full-rank lattice with `n ≥ 1` the set is nonempty and the infimum is attained, so it is the
paper's minimum; for `n = 0` it is `sInf ∅ = 0`. -/
noncomputable def lam1 {n : ℕ} (L : Submodule ℤ (E n)) : ℝ :=
  sInf {r : ℝ | ∃ v ∈ L, v ≠ 0 ∧ ‖v‖ = r}

/-- The point count `N_L(R) = |{v ∈ L ∖ {0} : ‖v‖ ≤ R}|` (§2.1, p.14; (A.2), p.87). Appendix A's
`C_L(T)` is `N_L(√T)`.

**Formalization Note.** The count is an extended natural number (`Set.encard`), so it never
collapses to `0` on an infinite set. -/
noncomputable def pointCount {n : ℕ} (L : Submodule ℤ (E n)) (R : ℝ) : ℕ∞ :=
  {v : E n | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ ≤ R}.encard

/-- The point-count bound (2.3) for one lattice in dimension `n` (§2.1, p.14): with `b = 2^β`,
`N_L(r·λ₁(L)) ≤ A_n bⁿ rⁿ` for every `r ≥ 1`.

**Formalization Note.** `A : ℕ → ℝ` is the family's prefactor sequence, evaluated at the
dimension `n` of `L`; `bⁿ` is written `2^{βn}`. The comparison is in `ℝ≥0∞`. The paper's family
condition `A_n = 2^{o(n)}` is stated where it is used, not here. -/
def PointCountBound {n : ℕ} (L : Submodule ℤ (E n)) (A : ℕ → ℝ) (β : ℝ) : Prop :=
  ∀ r : ℝ, 1 ≤ r →
    (pointCount L (r * lam1 L) : ℝ≥0∞) ≤ ENNReal.ofReal (A n * (2 : ℝ) ^ (β * n) * r ^ n)

/-- The Gaussian mass `ρ_s(S) = ∑_{x ∈ S} ρ_s(x)` of a (discrete) set `S ⊆ ℝⁿ`, with
`ρ_s(x) = e^{−π‖x‖²/s²}` (§2.2, p.16).

**Formalization Note.** The sum is an unconditional sum in `ℝ≥0∞` (a sum of nonnegative terms),
so it never collapses to `0` on a non-summable family; for lattices and their subsets and cosets it
is finite. `ρ_s` is the published `RegevLWE.GaussConv.rho`. -/
noncomputable def rhoSet {n : ℕ} (s : ℝ) (S : Set (E n)) : ℝ≥0∞ :=
  ∑' x : S, ENNReal.ofReal (RegevLWE.GaussConv.rho s (x : E n))

/-- The Gaussian sum `Z_σ(L) = ∑_{v ∈ L} e^{−‖v‖²/(2σ²)}` of Appendix A ((A.35), p.91).

**Formalization Note.** This is the variance-`σ²` convention of Appendix A, not the width-`s`
convention of `ρ_s` (they are related by `s = √(2π)σ`, p.17). Unconditional sum in `ℝ≥0∞`. -/
noncomputable def Zsig {n : ℕ} (σ : ℝ) (L : Submodule ℤ (E n)) : ℝ≥0∞ :=
  ∑' v : L, ENNReal.ofReal (Real.exp (-(‖(v : E n)‖ ^ 2) / (2 * σ ^ 2)))

end SuperlatSVP


