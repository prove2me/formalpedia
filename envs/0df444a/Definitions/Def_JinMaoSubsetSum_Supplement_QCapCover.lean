-- Prove2me | Definitions.Def_JinMaoSubsetSum_Supplement_QCapCover
-- name    : JinMaoSubsetSum_Supplement_QCapCover
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:53:55.180202+00:00
-- url     : https://prove2.me/theorems/ea0960c8-084c-4c51-ac77-2a8574ffdaf5
-- title:
--   Quotient cap coverings — real caps, $D=\rho(K-K)/2$, $r=\rho\,\mathrm{vol}_d(\pi_\Lambda K)/\mathrm{vol}_d(\pi_\Lambda D)$ and properties (i)–(v)
-- statement:
--   Let $K\subseteq\mathbb R^d$ be a convex body, $\Lambda\subseteq\mathbb R^d$ a lattice and $0<\rho<1$. Write
--   $$
--   D=\frac{\rho}{2}(K-K),\qquad r=\frac{\rho\,\mathrm{vol}_d(\pi_\Lambda K)}{\mathrm{vol}_d(\pi_\Lambda D)},
--   $$
--   where $K-K=\{x-y:x,y\in K\}$ is the Minkowski difference set and $\mathrm{vol}_d(\pi_\Lambda\cdot)$ is the volume of the image in $\mathbb R^d/\Lambda$.
--
--   A **parallelepiped** is $P=\{c+\sum_{j=1}^dt_je_j:|t_j|\le1\}$ with center $c\in\mathbb R^d$ and edge vectors $e_1,\dots,e_d\in\mathbb R^d$; a **cap** of $K$ is $Q=K\cap\{x:\langle u,x\rangle\ge a\}$ with $u\in\mathbb R^d$, $a\in\mathbb R$, here always paired with a parallelepiped $P$.
--
--   Given constants $c_d$, $C$, $\beta$, a list of caps $(Q_i,P_i)$ and a finite list of points $R$ form a **quotient cap covering** of $K$ if
--
--   1. there are at most $Cr$ caps and $|R|\le Cr$;
--   2. $Q_i\subseteq P_i$ for every $i$;
--   3. (i) $\sum_i\mathrm{vol}_d(\pi_\Lambda P_i)\le C\rho\,\mathrm{vol}_d(\pi_\Lambda K)$;
--   4. (ii) each $Q_i$ contains a translate of $c_dD$;
--   5. (iii) $K\setminus\bigcup_iQ_i\subseteq(K\ominus D)+\Lambda$;
--   6. (iv) $R+4d\lceil\beta\rceil D\subseteq K$;
--   7. (v) $\big(K\setminus\bigcup_iQ_i\big)\cap\big(\bigcup_iP_i+D+\Lambda\big)\subseteq R+D+\Lambda$.
--
--   These are the conclusions of Theorem 9.1; the definition lets the existence clause and the algorithmic clause of that theorem state them once.
--
--   **Formalization Note** `RPar`/`RCap` are the real counterparts of the published rational `ParOut`/`CapOut` (`CapOut.toRCap` casts a rational cap; the point sets agree). The edge vectors are not required to be independent, as in the paper. `dSet K ρ` is $D$; `rVal Λ K ρ` is $r$, computed in $[0,\infty]$ with the published `qvol` and converted to a real number (both volumes are finite and positive for a lattice of rank $<d$ and a convex body; a degenerate value would give $r=0$, which only makes the bounds harder). The parameter $\beta$ is the constant $\beta_d$ of Lemma 6.8; Theorem 9.1 uses $\beta_d=3d(d+1)$. $R$ is a list and $|R|$ its length, which bounds the number of distinct points. All sums of sets are Minkowski sums, $K\ominus D$ is the published `erosion`.
-- source:
--   Jin, Mao, Subset Sum in Almost-Linear Time, arXiv:2610.20742v1 (sha256 8b604948862d9188e922b8abf95831fde3a3699e26d39177d20a1460e31a926a), Theorem 9.1, p.48 (PDF p.50); Lemma 6.8, p.32 (PDF p.34)

import Mathlib
import Definitions.Def_JinMaoSubsetSum_zonotope
import Definitions.Def_JinMaoSubsetSum_qvol
import Definitions.Def_JinMaoSubsetSum_CapOut

set_option autoImplicit false

open scoped Pointwise

namespace JinMaoSubsetSum.Supplement

/-!
# Quotient cap coverings (the five properties of Theorem 9.1)

Jin, Mao, *Subset Sum in Almost-Linear Time*, arXiv:2610.20742v1, Theorem 9.1, p.48 (PDF p.50):
"Given a lattice Λ ⊆ ℝ^d of rank d′ < d, a convex body K ⊆ ℝ^d, and 0 < ρ < 1, write
D = ρ(K − K)/2 and r = ρ vol_d(π_Λ K)/ vol_d(π_Λ D). Then, there exist a collection of O_d(r) caps
Q_i = K ∩ {x : ⟨u_i, x⟩ ≥ a_i} with enclosing parallelepipeds P_i ⊇ Q_i, and a point set R ⊆ ℝ^d
of size |R| = O_d(r), such that the following properties hold: (i) Σ_i vol_d(π_Λ P_i) ≤ O_d(ρ)
vol_d(π_Λ K), (ii) each Q_i contains a translate of c_d D, for some 0 < c_d ≤ 1 depending only on
d, (iii) K \ ⋃_i Q_i ⊆ (K ⊖ D) + Λ, (iv) R + 4dβD ⊆ K, where β = ⌈β_d⌉ for the constant β_d in
Lemma 6.8, (v) and (K \ ⋃_i Q_i) ∩ (⋃_i P_i + D + Λ) ⊆ R + D + Λ." Lemma 6.8, p.32 (PDF p.34):
"Let K ⊆ ℝ^d be a convex body. There are an origin-symmetric parallelepiped B and a point c such
that c + B ⊆ K ⊆ c + β_d B for some β_d ≥ 1 depending only on d."

**Formalization Note.**
* `ℝ^d` is `Fin d → ℝ`; `⟨u, x⟩ = Σ_j u_j x_j`. `K − K`, `t • A`, `A + B` and `A + Λ` are
  pointwise (Minkowski) operations on sets; `K ⊖ D` is the published `erosion K D`.
* `RPar` is a parallelepiped `{c + Σ_j t_j e_j : |t_j| ≤ 1}` with real center `c` and `d` real
  edge vectors `e_1, …, e_d` (not required to be independent, as on the page); `RCap` is a cap
  `K ∩ {x : ⟨u, x⟩ ≥ a}` (real `u`, `a`) together with its parallelepiped. These are the real
  versions of the published rational `ParOut` / `CapOut`; `CapOut.toRCap` casts one to the
  other, with the same point sets.
* `dSet K ρ = (ρ/2) • (K − K)` is `D = ρ(K − K)/2`.
* `rVal Λ K ρ = ρ vol_d(π_Λ K) / vol_d(π_Λ D)`, computed in `ℝ≥0∞` with the published `qvol` and
  converted to a real number. For a discrete `Λ` of rank `< d` and a convex body `K` both volumes
  are finite and positive, so this is the paper's `r`. (Were a volume `0` or `∞`, `rVal` would be
  `0`, which makes every bound `≤ C · rVal` harder, never easier.)
* `β` is the constant `β_d` of Lemma 6.8; Theorem 9.1 passes `β_d = 3d(d + 1)`, the value of
  the proof of Lemma 6.8 (p.33).
* `QCapCover d Λ K ρ cd C β caps R` lists, for the caps `caps` and the points `R` (a list; `|R|`
  is its length, which bounds the number of distinct points), the conclusions of Theorem 9.1:
  the counts `|caps| ≤ C r` and `|R| ≤ C r`, `Q_i ⊆ P_i`, and properties (i)–(v) with
  `O_d(ρ) = Cρ` and `β = ⌈β_d⌉`.
-/

/-- A parallelepiped `{c + Σ_j t_j e_j : |t_j| ≤ 1}` with real center and edges. -/
structure RPar (d : ℕ) where
  center : Fin d → ℝ
  edge : Fin d → Fin d → ℝ

/-- The point set of a real parallelepiped. -/
def RPar.toSet {d : ℕ} (P : RPar d) : Set (Fin d → ℝ) :=
  {x | ∃ t : Fin d → ℝ, (∀ j, |t j| ≤ 1) ∧ x = P.center + ∑ j, t j • P.edge j}

/-- A real cap `K ∩ {x : ⟨u, x⟩ ≥ a}` (normal `u`, offset `a`) with an enclosing parallelepiped. -/
structure RCap (d : ℕ) where
  u : Fin d → ℝ
  a : ℝ
  par : RPar d

/-- The cap `Q = K ∩ {x : ⟨u, x⟩ ≥ a}` of `K`. -/
def RCap.capSet {d : ℕ} (Q : RCap d) (K : Set (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  K ∩ {x | Q.a ≤ ∑ j, Q.u j * x j}

/-- The real cap of a rational cap (same normal, offset, center and edges). -/
def _root_.JinMaoSubsetSum.CapOut.toRCap {d : ℕ} (Q : CapOut d) : RCap d :=
  ⟨qToR Q.u, (Q.a : ℝ), ⟨qToR Q.par.center, fun j => qToR (Q.par.edge j)⟩⟩

/-- `D = ρ(K − K)/2`. -/
def dSet {d : ℕ} (K : Set (Fin d → ℝ)) (ρ : ℝ) : Set (Fin d → ℝ) :=
  (ρ / 2) • (K - K)

/-- `r = ρ vol_d(π_Λ K) / vol_d(π_Λ D)` as a real number. -/
noncomputable def rVal {d : ℕ} (Λ : AddSubgroup (Fin d → ℝ)) (K : Set (Fin d → ℝ)) (ρ : ℝ) : ℝ :=
  (ENNReal.ofReal ρ * qvol Λ K / qvol Λ (dSet K ρ)).toReal

/-- The conclusions of Theorem 9.1 for caps `caps` and points `R`, with constants `cd`
(property (ii)), `C` (every `O_d(·)`) and `β` (the constant `β_d` of Lemma 6.8). -/
def QCapCover (d : ℕ) (Λ : AddSubgroup (Fin d → ℝ)) (K : Set (Fin d → ℝ)) (ρ cd C β : ℝ)
    (caps : List (RCap d)) (R : List (Fin d → ℝ)) : Prop :=
  -- O_d(r) caps and |R| = O_d(r)
  (caps.length : ℝ) ≤ C * rVal Λ K ρ ∧
  (R.length : ℝ) ≤ C * rVal Λ K ρ ∧
  -- enclosing parallelepipeds P_i ⊇ Q_i
  (∀ Q ∈ caps, Q.capSet K ⊆ Q.par.toSet) ∧
  -- (i) Σ_i vol_d(π_Λ P_i) ≤ O_d(ρ) vol_d(π_Λ K)
  (caps.map (fun Q => qvol Λ Q.par.toSet)).sum ≤ ENNReal.ofReal (C * ρ) * qvol Λ K ∧
  -- (ii) each Q_i contains a translate of c_d D
  (∀ Q ∈ caps, ∃ x : Fin d → ℝ, (fun y => x + y) '' (cd • dSet K ρ) ⊆ Q.capSet K) ∧
  -- (iii) K \ ⋃_i Q_i ⊆ (K ⊖ D) + Λ
  K \ (⋃ Q ∈ caps, Q.capSet K) ⊆ erosion K (dSet K ρ) + (Λ : Set (Fin d → ℝ)) ∧
  -- (iv) R + 4dβD ⊆ K with β = ⌈β_d⌉
  {x | x ∈ R} + (4 * (d : ℝ) * (⌈β⌉₊ : ℝ)) • dSet K ρ ⊆ K ∧
  -- (v) (K \ ⋃_i Q_i) ∩ (⋃_i P_i + D + Λ) ⊆ R + D + Λ
  (K \ (⋃ Q ∈ caps, Q.capSet K)) ∩
      ((⋃ Q ∈ caps, Q.par.toSet) + dSet K ρ + (Λ : Set (Fin d → ℝ))) ⊆
    {x | x ∈ R} + dSet K ρ + (Λ : Set (Fin d → ℝ))

end JinMaoSubsetSum.Supplement


