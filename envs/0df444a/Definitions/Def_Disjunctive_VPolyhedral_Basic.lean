-- Prove2me | Definitions.Def_Disjunctive_VPolyhedral_Basic
-- name    : Disjunctive_VPolyhedral_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T17:05:23.674977+00:00
-- url     : https://prove2.me/theorems/b5516a31-8a7d-45e6-ab14-170ec9cf47ba
-- title:
--   The V-polyhedral system, the disjunctive cone, and the CGLP/GIC apparatus
-- statement:
--   This definition collects the V-polyhedral, disjunctive-cone, and CGLP/GIC vocabulary
--   Chapter 12's results are built from.
--
--   `ConicHull S` is the set of finite nonnegative combinations of elements of `S`. `Ph h :=
--   convV^h + coneR^h` is the vertex-ray representation of the `h`-th disjunct, `DisjSet := ⋃_h
--   P^h` the resulting disjunctive set. `CombinedC` is the *single* polyhedron
--   $\mathrm{conv}(\bigcup_h \tilde V^h) + \mathrm{cone}(\bigcup_h \tilde R^h)$ obtained from a
--   relaxed vertex-ray system (distinct from `DisjSet`, which is a *union* of per-disjunct
--   pieces). `IsVPolyhedralValid` packages the validity conditions `αp≥β`/`αr≥0` shared by
--   Proposition 12.1 (eq. (12.3)) and Theorem 12.4 (eq. (12.8)).
--
--   `DisjunctiveCone` is the homogenized, translated disjunctive cone `C_{x_F}` centered at a
--   point `x_F`. `IsCGLP129Feasible` is the lift-and-project cut-generating LP (12.9). `IsGICFromS`
--   packages "is a generalized intersection cut from `S`" as the two properties Theorem 11.4's
--   surrounding remark identifies GICs with: valid outside `int S`, and a genuine cut of `P`.
--
--   **Formalization Note.** `Ph`/`DisjSet`/`IsVPolyhedralValid` are stated generically enough to
--   serve both Proposition 12.1's `V^h`/`R^h` and Theorem 12.4's `Ṽ^h`/`R̃^h` (per `BRIEF.md`'s
--   explicit warning that these are different objects) — the same definitions, applied to
--   different vertex/ray data, rather than two separately named but structurally identical
--   definitions.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 195, 199, 206-207, Sections 12, 12.1.1, 12.2

import Mathlib

namespace Disjunctive.VPolyhedral

/-- The conic (positive) hull of a set `S`: all finite nonnegative combinations of elements of
`S` (Balas §12.1.1, p. 199, `cone(·)`). -/
def ConicHull {E : Type*} [AddCommGroup E] [Module ℝ E] (S : Set E) : Set E :=
  {x | ∃ (k : ℕ) (c : Fin k → ℝ) (v : Fin k → E),
    (∀ i, 0 ≤ c i) ∧ (∀ i, v i ∈ S) ∧ x = ∑ i, c i • v i}

/-- `P^h := convV^h + coneR^h`, the V-polyhedral (vertex-ray) representation of the `h`-th
disjunct (Balas §12, p. 195, eq. (12.2)), given finite index types `Vidx h`/`Ridx h` enumerating
its vertices/extreme rays. -/
def Ph {n : ℕ} {Q : Type*} (Vidx Ridx : Q → Type*) [∀ h, Fintype (Vidx h)]
    [∀ h, Fintype (Ridx h)] (vpt : ∀ h, Vidx h → Fin n → ℝ) (rvec : ∀ h, Ridx h → Fin n → ℝ)
    (h : Q) : Set (Fin n → ℝ) :=
  {x | ∃ (lam : Vidx h → ℝ) (mu : Ridx h → ℝ), (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1 ∧
    (∀ i, 0 ≤ mu i) ∧ x = (∑ i, lam i • vpt h i) + ∑ i, mu i • rvec h i}

/-- The disjunctive set `F := ⋃_{h∈Q} P^h` (Balas §12, p. 195). -/
def DisjSet {n : ℕ} {Q : Type*} (Vidx Ridx : Q → Type*) [∀ h, Fintype (Vidx h)]
    [∀ h, Fintype (Ridx h)] (vpt : ∀ h, Vidx h → Fin n → ℝ) (rvec : ∀ h, Ridx h → Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  ⋃ h, Ph Vidx Ridx vpt rvec h

/-- The combined polyhedron `C := conv(∪_h Ṽ^h) + cone(∪_h R̃^h)` (Balas §12.2, p. 206, used in
Theorem 12.4's proof and Theorem 12.5's statement). -/
def CombinedC {n : ℕ} {Q : Type*} (Vidx Ridx : Q → Type*) [∀ h, Fintype (Vidx h)]
    [∀ h, Fintype (Ridx h)] (vpt : ∀ h, Vidx h → Fin n → ℝ) (rvec : ∀ h, Ridx h → Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {x | ∃ p ∈ convexHull ℝ (⋃ h, Set.range (vpt h)),
    ∃ r ∈ ConicHull (⋃ h, Set.range (rvec h)), x = p + r}

/-- `(α,β)` is valid for the combined system: `αp≥β` for every vertex, `αr≥0` for every ray, over
all `h ∈ Q` (Balas §12, p. 195, eq. (12.3), and §12.2, p. 206, eq. (12.8) for the tilded system).
-/
def IsVPolyhedralValid {n : ℕ} {Q : Type*} (Vidx Ridx : Q → Type*) [∀ h, Fintype (Vidx h)]
    [∀ h, Fintype (Ridx h)] (vpt : ∀ h, Vidx h → Fin n → ℝ) (rvec : ∀ h, Ridx h → Fin n → ℝ)
    (alpha : Fin n → ℝ) (beta : ℝ) : Prop :=
  (∀ h, ∀ p, beta ≤ dotProduct alpha (vpt h p)) ∧ (∀ h, ∀ r, 0 ≤ dotProduct alpha (rvec h r))

/-- The disjunctive cone `C_{x_F}` (Balas §12.1.1, p. 199): the homogenization, at `x_F`, of the
translated disjunctive polyhedron `Ax'+(Ax_F-b)x_0'≥0 ∧ ⋁_h(D^hx'+(D^hx_F-d^h_0)x_0'≥0)`. -/
def DisjunctiveCone {n m : ℕ} {Q : Type*} {Rh : Q → ℕ} (Atil : Matrix (Fin m) (Fin n) ℝ)
    (btil : Fin m → ℝ) (Dh : ∀ h, Matrix (Fin (Rh h)) (Fin n) ℝ) (d0h : ∀ h, Fin (Rh h) → ℝ)
    (xF : Fin n → ℝ) : Set ((Fin n → ℝ) × ℝ) :=
  {p | 0 ≤ p.2 ∧ (∀ i, 0 ≤ (Atil.mulVec p.1 + p.2 • (Atil.mulVec xF - btil)) i) ∧
    ∃ h, ∀ i, 0 ≤ ((Dh h).mulVec p.1 + p.2 • ((Dh h).mulVec xF - d0h h)) i}

/-- The L&P cut-generating LP (12.9) (Balas §12.2, p. 207): `α = u^h D̃^h`, `β ≤ u^h d̃^h_0` for
every `h ∈ Q`, normalized by `Σ_h u^he = 1`, `u^h ≥ 0`. -/
def IsCGLP129Feasible {n : ℕ} {Q : Type*} [Fintype Q] {Rh : Q → ℕ}
    (Dtil : ∀ h, Matrix (Fin (Rh h)) (Fin n) ℝ) (d0til : ∀ h, Fin (Rh h) → ℝ)
    (alpha : Fin n → ℝ) (u : ∀ h, Fin (Rh h) → ℝ) (beta : ℝ) : Prop :=
  (∀ h, alpha = Matrix.vecMul (u h) (Dtil h)) ∧ (∀ h, beta ≤ dotProduct (u h) (d0til h)) ∧
    (∑ h, ∑ i, u h i) = 1 ∧ ∀ h i, 0 ≤ u h i

/-- `(α,β)` is (the halfspace of) a generalized intersection cut from `S := {x : u^hD̃^hx ≤
u^hd̃^h_0, h∈Q}` relative to `P` (Balas §11.3-11.4, restated locally): valid for `P` outside
`int S`, and a genuine cut (violated somewhere on `P`). -/
def IsGICFromS {n : ℕ} {Q : Type*} [Fintype Q] {Rh : Q → ℕ}
    (Dtil : ∀ h, Matrix (Fin (Rh h)) (Fin n) ℝ) (d0til : ∀ h, Fin (Rh h) → ℝ)
    (P : Set (Fin n → ℝ)) (u : ∀ h, Fin (Rh h) → ℝ) (alpha : Fin n → ℝ) (beta : ℝ) : Prop :=
  (∀ x ∈ P, (¬ ∀ h, dotProduct (u h) ((Dtil h).mulVec x) < dotProduct (u h) (d0til h)) →
      beta ≤ dotProduct alpha x) ∧
    ∃ x ∈ P, dotProduct alpha x < beta

end Disjunctive.VPolyhedral


