-- Prove2me | Definitions.Def_RamseyLST_Main_MetricComposition
-- name    : RamseyLST_Main_MetricComposition
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:08:15.818208+00:00
-- url     : https://prove2.me/theorems/e064c7df-e7b7-4c23-a1c2-c7445781d588
-- title:
--   Metric compositions $M_\beta[N]$ and the class $\mathrm{comp}_\beta(\Phi)$ (Definition 5)
-- statement:
--   Let $\mathcal N(\Phi)$ be the class of finite metric spaces with aspect ratio at most $\Phi$. For a finite metric space $M$ with $|M|\ge2$, a family $N=\{N_x\}_{x\in M}$ of metric spaces and $\beta'$, the **$\beta'$-composition** $H=M_{\beta'}[N]$ (Definition 5) has as points the disjoint union of the $N_x$, with
--
--   $$d_H(u,v)=\begin{cases}d_{N_x}(u,v), & u,v\in N_x,\\ \beta'\gamma\,d_M(x,y), & u\in N_x,\ v\in N_y,\ x\neq y,\end{cases}\qquad \gamma=\frac{\max_{x\in M}\operatorname{diam}(N_x)}{\min_{x\neq y\in M}d_M(x,y)}.$$
--
--   The class $\mathrm{comp}_\beta(\Phi)$ is the closure of $\mathcal N(\Phi)$ under compositions $M_{\beta'}[N]$ with $M\in\mathcal N(\Phi)$, every $N_x\in\mathrm{comp}_\beta(\Phi)$ and $\beta'\ge\beta$. As Definition 5 prescribes, a space of $\mathrm{comp}_\beta(\Phi)$ always comes with a fixed representation.
--
--   A representation is either a base space $(P,d)\in\mathcal N(\Phi)$, or a composition of $(M,d_M)$ with $|M|\ge2$ and $\Phi(M)\le\Phi$, a parameter $\beta'\ge\max(\beta,1/2)$ and a family of representations $N_x$. Its points and its distance $d_H$ are computed recursively by the formula above.
--
--   These spaces are the targets of Lemmas 7 and 8.
--
--   **Formalization Note** Raw composition data form an inductive type `CompRep β Φ` with a `carrier` type of points and a realised distance `dist`. The composition case does not exclude $\gamma=0$ (every $N_x$ a single point), in which case $d_H$ vanishes off the diagonal; that case is the slip recorded as insight I1. To represent a metric space in the class, the raw data H must also satisfy `IsMetric H.dist`, as explicitly required by Lemmas 7 and 8. Non-contractivity alone only constrains the image of an embedding and does not ensure that the entire target is a metric. The composition constructor retains the printed domain $\beta'\ge1/2$. $\operatorname{diam}(N_x)$ is a real supremum over the (finite) points of $N_x$, which is $0$ when $N_x$ is empty.
-- source:
--   Bartal, Hovav, Nearly Tight Low-Stretch Ramsey Spanning Trees, STOC 2027 submission (manuscript sha256 bcaed0afb9db0cccb453599c9f6915e958922563d3989766c4affc99a15de44d), p. 11 (PDF 15), Definition 5

import Mathlib
import Definitions.Def_RamseyLST_Main_FiniteMetric

namespace RamseyLST.Main

/-- Definition 5 (p. 11): raw composition data for a space of `comp_β(Φ) = comp_β(N(Φ))`, where
`N(Φ)` is the class of finite metric spaces of aspect ratio at most `Φ`.
* `base`: a finite metric space `(P, d)` with `Φ(P) ≤ Φ` (level 0);
* `comp`: the composition `M_{β'}[N]` of a finite metric space `M ∈ N(Φ)` with `|M| ≥ 2`, a
  family `N = {N_x}_{x ∈ M}` of represented spaces, and `β' ≥ max β (1/2)`.
The printed distance formula admits degenerate data (e.g. all singleton clouds).
A metric space in the class is represented by `H : CompRep β Φ` together with
`IsMetric H.dist`; Lemmas 7 and 8 require this explicitly. -/
inductive CompRep (β Φ : ℝ) : Type 1 where
  | base (P : Type) [Fintype P] (d : P → P → ℝ) (hd : IsMetric d)
      (hΦ : aspectRatio d Finset.univ ≤ Φ) : CompRep β Φ
  | comp (M : Type) [Fintype M] (dM : M → M → ℝ) (hM : IsMetric dM)
      (hcard : 2 ≤ Fintype.card M) (hΦ : aspectRatio dM Finset.univ ≤ Φ)
      (β' : ℝ) (hβ' : β ≤ β') (hhalf : (1 : ℝ) / 2 ≤ β') (N : M → CompRep β Φ) : CompRep β Φ

namespace CompRep

variable {β Φ : ℝ}

/-- The points of the represented space: those of the base space, or the disjoint union
`⨆_{x ∈ M} N_x` of the points of the composed spaces. -/
def carrier : CompRep β Φ → Type
  | base P _ _ _ => P
  | comp M _ _ _ _ _ _ _ N => Σ x : M, (N x).carrier

open Classical in
/-- The realised distance `d_H` of Definition 5: for `u ∈ N_x`, `v ∈ N_y`,
`d_H(u, v) = d_{N_x}(u, v)` if `x = y`, and `β' γ d_M(x, y)` if `x ≠ y`, where
`γ = max_{x ∈ M} diam(N_x) / min_{x ≠ y ∈ M} d_M(x, y)`. -/
noncomputable def dist : (H : CompRep β Φ) → H.carrier → H.carrier → ℝ
  | base _ d _ _, u, v => d u v
  | comp M dM _ _ _ β' _ _ N, ⟨x, u⟩, ⟨y, v⟩ =>
      if h : x = y then (N x).dist u (cast (congrArg (fun z => (N z).carrier) h.symm) v)
      else
        β' * ((⨆ z : M, ⨆ a, ⨆ b, (N z).dist a b) /
              (if hM : (Finset.univ : Finset M).offDiag.Nonempty then
                (Finset.univ : Finset M).offDiag.inf' hM (fun p => dM p.1 p.2) else 1)) *
          dM x y

end CompRep

end RamseyLST.Main


