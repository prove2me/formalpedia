-- Prove2me | Definitions.Def_StackingStars_Main_Bowl
-- name    : StackingStars_Main_Bowl
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:45:41.101235+00:00
-- url     : https://prove2.me/theorems/72e7501d-5146-4d42-ad37-78a8b5856ebc
-- title:
--   Bowls, separators, stacks, and the bowl Q_τ(P) = P ∪ q R_Q ∪ q L_Q of a star
-- statement:
--   * `IsBowl Q q L R d u h`: $Q$ is a bowl aligned along $(d,u)$ with height $h>0$, kernel point $q$ and arm ends $L,R$. This means $Q$ is polygonal (a finite union of convex hulls of finite vertex sets, allowing zero-width arms), $d,u$ are orthogonal unit vectors, $R$ is farthest from $q$ in $Q$, $L$ maximizes distance from the line $qR$, $q$ is in the kernel of $Q$, $L,R\in Q$ (the finite arms belong to the bowl), $d\cdot(L-q)=d\cdot(R-q)=h$, $u\cdot L<u\cdot R$, and $-h\le d\cdot(z-q)\le h$ for every $z\in Q$.
--   * `separator q L R u` $=\{L-tu:t\ge0\}\cup Lq\cup qR\cup\{R+tu:t\ge0\}$.
--   * `IsStack Q q L R d u h t`: all $Q_i$ are bowls with the specified reference points and common directions and height; the translated bowls $Q_i+t_i$ have pairwise disjoint interiors and their own translated separators are pairwise disjoint.
--   * For a star with reference data $D$ and fine type $\tau$ in the size group with scales $r,w$, with $h=100w$: `bowlR` $=R_Q$ is the point of the ray $q_P\to R_P$ with $d_\tau\cdot(R_Q-q_P)=h$, `bowlL` $=L_Q$ is the point of the ray $q_P\to L_P$ with $d_\tau\cdot(L_Q-q_P)=h$, and
--   $$Q_\tau(P)=P\cup q_PR_Q\cup q_PL_Q$$
--   is `bowl`, with separator `bowlSep` (taken with $u=u_\tau$).
--
--   **Formalization Note.** The paper calls a bowl a "(possibly weakly simple) star-shaped polygon". Polygonality is encoded as a finite union of finite convex hulls. Together with a kernel point this describes a star-shaped polygonal region, including zero-width arms and weak boundary contacts. The reference-point extrema are inherited from the final sentence on p. 14.
-- source:
--   Abrahamsen, Conradi, Khan, Stade, Wong, Yan, Zhang, Stacking Stars: Minimum-Area Packing with and without Rotation, STOC 2027 submission (manuscript sha256 ee9554eb…), pp. 14-16, §3.3 (bowls, separators, stacks, proof of Lemma 11)

import Mathlib
import Definitions.Def_StackingStars_Main_Geometry
import Definitions.Def_StackingStars_Main_StarPolygon
import Definitions.Def_StackingStars_Main_ReferenceData
import Definitions.Def_StackingStars_Main_FineType

namespace StackingStars.Main

/-!
# Bowls, separators, stacks, and the bowl `Q_τ(P)` of a star

Abrahamsen et al., *Stacking Stars*, STOC 2027 submission (manuscript sha256 ee9554eb…), §3.3,
p. 14 (PDF 16): "Let d, u be orthogonal unit vectors. We say that a (possibly weakly simple)
star-shaped polygon Q is a bowl aligned along (d, u) with height h > 0 if it has a specified kernel
point q_Q and specified points L_Q, R_Q such that d·(L_Q − q_Q) = d·(R_Q − q_Q) = h,
u·L_Q < u·R_Q, ∀z ∈ Q, −h ≤ d·(z − q_Q) ≤ h." p. 15 (PDF 17): "Separator(Q) = {L_Q − t u : t ≥ 0}
∪ L_Q q_Q ∪ q_Q R_Q ∪ {R_Q + t u : t ≥ 0}. We say that a packing of bowls with the same directions
d, u and height h forms a stack if their separators are pairwise disjoint." p. 16 (PDF 18), proof of
Lemma 11: "We extend the rays q_P R_P and q_P L_P to points R_Q and L_Q such that
d_τ·(R_Q − q_P) = d_τ·(L_Q − q_P) = h, and let the bowl Q = Q_τ(P) be P ∪ qR_Q ∪ qL_Q."

The finite arms `q_Q L_Q`, `q_Q R_Q` belong to the bowl (Figure 14), so `L_Q, R_Q ∈ Q`.
-/

/-- A bounded polygonal set, allowing zero-width arms: a finite union of convex hulls of
finite vertex sets. Together with a nonempty kernel this represents a possibly weakly simple
star-shaped polygon (triangulate the filled faces and include the zero-width edges). -/
def IsPolygonal (Q : Set Pt) : Prop :=
  ∃ (m : ℕ) (V : Fin m → Finset Pt), Q = ⋃ i, convexHull ℝ (V i : Set Pt)

/-- A polygonal bowl with orthogonal unit directions, and reference points with the
extremal properties inherited from §3.1, as stipulated at the end of p. 14. -/
def IsBowl (Q : Set Pt) (q L R d u : Pt) (h : ℝ) : Prop :=
  IsPolygonal Q ∧ len d = 1 ∧ len u = 1 ∧ dot d u = 0 ∧
    0 < h ∧ q ∈ kernel Q ∧ L ∈ Q ∧ R ∈ Q ∧
    (∀ z ∈ Q, len (z - q) ≤ len (R - q)) ∧
    (∀ z ∈ Q, |cross (R - q) (z - q)| ≤ |cross (R - q) (L - q)|) ∧
    dot d (L - q) = h ∧ dot d (R - q) = h ∧
    dot u L < dot u R ∧ ∀ z ∈ Q, -h ≤ dot d (z - q) ∧ dot d (z - q) ≤ h

/-- `Separator(Q) = {L − t u : t ≥ 0} ∪ Lq ∪ qR ∪ {R + t u : t ≥ 0}`. -/
def separator (q L R u : Pt) : Set Pt :=
  {x | ∃ t : ℝ, 0 ≤ t ∧ x = L - t • u} ∪ segment ℝ L q ∪ segment ℝ q R ∪
    {x | ∃ t : ℝ, 0 ≤ t ∧ x = R + t • u}

/-- Bowls with common directions and height form a stack when they pack and their own
separators are pairwise disjoint (p. 15). -/
def IsStack {ι : Type} (Q : ι → Set Pt) (q L R : ι → Pt) (d u : Pt) (h : ℝ)
    (t : ι → Pt) : Prop :=
  (∀ i, IsBowl (Q i) (q i) (L i) (R i) d u h) ∧
    (Pairwise fun i j => Disjoint (interior (translate (t i) (Q i)))
      (interior (translate (t j) (Q j)))) ∧
    Pairwise fun i j => Disjoint (translate (t i) (separator (q i) (L i) (R i) u))
      (translate (t j) (separator (q j) (L j) (R j) u))

namespace RefData

variable {S : Set Pt} (D : RefData S)

/-- `R_Q`: the point of the ray `q_P → R_P` with `d_τ·(R_Q − q_P) = h`, `h = 100 w`. -/
noncomputable def bowlR (r w : ℝ) (τ : FineType) : Pt :=
  D.q + (100 * w / dot (τ.d r w) (D.R - D.q)) • (D.R - D.q)

/-- `L_Q`: the point of the ray `q_P → L_P` with `d_τ·(L_Q − q_P) = h`, `h = 100 w`. -/
noncomputable def bowlL (r w : ℝ) (τ : FineType) : Pt :=
  D.q + (100 * w / dot (τ.d r w) (D.L - D.q)) • (D.L - D.q)

/-- The bowl `Q_τ(P) = P ∪ q R_Q ∪ q L_Q` (proof of Lemma 11, p. 16). -/
def bowl (r w : ℝ) (τ : FineType) : Set Pt :=
  S ∪ segment ℝ D.q (D.bowlR r w τ) ∪ segment ℝ D.q (D.bowlL r w τ)

/-- `Separator(Q_τ(P))`, with `u = u_τ`. -/
noncomputable def bowlSep (r w : ℝ) (τ : FineType) : Set Pt :=
  separator D.q (D.bowlL r w τ) (D.bowlR r w τ) (τ.u r w)

end RefData

end StackingStars.Main


