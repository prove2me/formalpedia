-- Prove2me | Definitions.Def_BipColorHard_Connector
-- name    : BipColorHard_Connector
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:34:38.167515+00:00
-- url     : https://prove2.me/theorems/97abdb17-2609-4293-88bb-debcf13565ac
-- title:
--   The connector $K(s)$, its weights $K(B,A)$ and $K_L(B,A)$, and the conclusions of Lemmas 10 and 11
-- statement:
--   Fix disjoint $A_0,B_0\in\Omega$ and let $X=\{B\in\Omega:B\cap A_0=\emptyset\}$, $Y=\{A\in\Omega:A\cap B_0=\emptyset\}$. The **connector** $K(s)$ is a bipartite graph with terminals $z_R$ (right) and $z_L$ (left) and two reference vertices, one on each side.
--
--   The right arm has right vertices $r_0=z_R,r_1,\dots,r_s$. For $i=1,\dots,s$, a copy of $K_{3,2}$ whose side of size three contains $r_{i-1}$ and $r_i$ joins them, and a path of length two joins $r_i$ to the right reference vertex. The left arm is the mirror image, on $l_0=z_L,\dots,l_s$, and the central edge is $\{r_s,l_s\}$. All internal vertices are new and distinct.
--
--   $K(B,A)$ is the number of label assignments with $z_R=B$, $z_L=A$, reference labels $B_0$ on the right and $A_0$ on the left, and disjoint labels on every edge. $K_L(B,A)$ is the total weight of the multigraph in which every edge is replaced by $L$ parallel edges of interaction $W_u$, with the same terminal and reference labels.
--
--   For a weight function $f$ on $X\times Y$, `ConnCorr` is the conclusion of Lemma 10: $f>0$, and for $(B,A)$ chosen with probability proportional to $f(B,A)$,
--   $$\Pr[B=B_0]=\Pr[A=A_0],\qquad \Pr[B=B_0,A=A_0]>\Pr[B=B_0]\Pr[A=A_0].$$
--   `ConnAntiferro` is the conclusion of Lemma 11: there are $b>0$, $\theta>1$ such that the two connectors between blocks with values $\sigma(v),\sigma(w)$ have total weight $b^2$ if the values agree and $b^2\theta$ otherwise. In the connector from $v$ to $w$, $z_R=B_0$ if $\sigma(v)=1$ and ranges over $X$ if $\sigma(v)=0$; $z_L=A_0$ if $\sigma(w)=0$ and ranges over $Y$ if $\sigma(w)=1$.
--
--   The connector turns the same-side ferromagnetic tendency of the model into the antiferromagnetic interaction between blocks that encodes MAX-CUT.
--
--   **Formalization Note** The vertices are explicit inductive types and edges are listed as (left end, right end). Probabilities are written as ratios of sums.
-- source:
--   Galanis, Guo, He, Štefankovič, Vigoda, NP-hardness for Bipartite Colorings up to the Maximum Degree, manuscript of Nov. 3, 2026 (sha256 78a66d1f…), §3.2.1, p.8 (PDF p.10); §3.2.2, pp.9–11 (PDF pp.11–13); §5.1, p.20 (PDF p.22); Lemmas 10, 11

import Definitions.Def_BipColorHard_PhaseLabeling

set_option autoImplicit false

namespace BipColorHard

/-- Internal left vertices of the connector `K(s)` (Galanis, Guo, He, Štefankovič, Vigoda, manuscript of
Nov. 3, 2026 (sha256 78a66d1f…), §5.1, p.20 (PDF p.22)): `l i` is the arm vertex `l_{i+1}`; `lThird i` is
the third vertex of the side of size three of the left-arm copy of `K_{3,2}` between `l_i`, `l_{i+1}`;
`rPair i j` are the two vertices of the side of size two of the right-arm copy between `r_i`, `r_{i+1}`;
`rMid i` is the middle vertex of the path of length two from `r_{i+1}` to the right reference. -/
inductive ConnLInt (s : ℕ) : Type
  | l (i : Fin s)
  | lThird (i : Fin s)
  | rPair (i : Fin s) (j : Fin 2)
  | rMid (i : Fin s)
  deriving DecidableEq, Fintype

/-- Internal right vertices of `K(s)`, the mirror image of `ConnLInt`. -/
inductive ConnRInt (s : ℕ) : Type
  | r (i : Fin s)
  | rThird (i : Fin s)
  | lPair (i : Fin s) (j : Fin 2)
  | lMid (i : Fin s)
  deriving DecidableEq, Fintype

/-- Left vertices of `K(s)`: the left terminal `z_L = l_0`, the left reference vertex, and the internal ones. -/
inductive ConnLV (s : ℕ) : Type
  | zL
  | lRef
  | int (x : ConnLInt s)
  deriving DecidableEq, Fintype

/-- Right vertices of `K(s)`: the right terminal `z_R = r_0`, the right reference vertex, and the internal ones. -/
inductive ConnRV (s : ℕ) : Type
  | zR
  | rRef
  | int (x : ConnRInt s)
  deriving DecidableEq, Fintype

/-- The arm vertex `l_i`, `i = 0, …, s`. -/
def lAt (s : ℕ) : Fin (s + 1) → ConnLV s := Fin.cases .zL fun i => .int (.l i)

/-- The arm vertex `r_i`, `i = 0, …, s`. -/
def rAt (s : ℕ) : Fin (s + 1) → ConnRV s := Fin.cases .zR fun i => .int (.r i)

/-- The edges of the connector `K(s)`, §5.1, p.20 (PDF p.22), each as (left end, right end). For each
`i < s`: the copy of `K_{3,2}` whose side of size three is `{r_i, r_{i+1}, rThird i}` and whose side of size
two is `{rPair i 0, rPair i 1}`; the path of length two from `r_{i+1}` to the right reference; the mirror
images in the left arm; and finally the central edge `{r_s, l_s}`. -/
def connEdges (s : ℕ) : List (ConnLV s × ConnRV s) :=
  ((List.finRange s).flatMap fun i =>
    ((List.finRange 2).flatMap fun j =>
      [(.int (.rPair i j), rAt s i.castSucc), (.int (.rPair i j), rAt s i.succ),
        (.int (.rPair i j), .int (.rThird i)),
        (lAt s i.castSucc, .int (.lPair i j)), (lAt s i.succ, .int (.lPair i j)),
        (.int (.lThird i), .int (.lPair i j))]) ++
    [(.int (.rMid i), rAt s i.succ), (.int (.rMid i), .rRef),
      (lAt s i.succ, .int (.lMid i)), (.lRef, .int (.lMid i))]) ++
  [(lAt s (Fin.last s), rAt s (Fin.last s))]

/-- `X = {B ∈ Ω : B ∩ A₀ = ∅}`, §3.2.1, p.8 (PDF p.10). -/
def setX (k : ℕ) (A0 : Omega k) : Finset (Omega k) :=
  Finset.univ.filter fun B => Disjoint B.1 A0.1

/-- `Y = {A ∈ Ω : A ∩ B₀ = ∅}`, §3.2.1, p.8 (PDF p.10). -/
def setY (k : ℕ) (B0 : Omega k) : Finset (Omega k) :=
  Finset.univ.filter fun A => Disjoint A.1 B0.1

/-- `K(B, A)`, §3.2.2, p.9 (PDF p.11): the number of label assignments to `K(s)` in which `z_R` has
label `B`, `z_L` has label `A`, the reference vertices have their prescribed labels `B₀`, `A₀`, and the two
ends of every edge have disjoint labels. -/
noncomputable def connK (k s : ℕ) (A0 B0 B A : Omega k) : ℝ :=
  (Nat.card {σ : (ConnLV s → Omega k) × (ConnRV s → Omega k) //
    σ.2 .zR = B ∧ σ.1 .zL = A ∧ σ.2 .rRef = B0 ∧ σ.1 .lRef = A0 ∧
      ∀ e ∈ connEdges s, Disjoint (σ.1 e.1).1 (σ.2 e.2).1} : ℝ)

/-- `K_L(B, A)`, §3.2.2, p.10 (PDF p.12): the total weight of the multigraph obtained from `K(s)` by
replacing every edge by `L` parallel edges with interaction `W_u`, with terminal labels `B`, `A` and the
prescribed reference labels. -/
noncomputable def connKL (k s : ℕ) (u : ℝ) (L : ℕ) (A0 B0 B A : Omega k) : ℝ :=
  ∑ σL : ConnLV s → Omega k, ∑ σR : ConnRV s → Omega k,
    if σR .zR = B ∧ σL .zL = A ∧ σR .rRef = B0 ∧ σL .lRef = A0 then
      ((connEdges s).map fun e => W k u (σL e.1) (σR e.2) ^ L).prod
    else 0

/-- The conclusion of Lemma 10 (pp.10–11, PDF pp.12–13) for a weight function `f` on terminal labels:
`f(B, A) > 0` for all `B ∈ X`, `A ∈ Y`, and for `(B, A) ∈ X × Y` chosen with probability proportional to
`f(B, A)`, `Pr[B = B₀] = Pr[A = A₀]` and `Pr[B = B₀, A = A₀] > Pr[B = B₀] Pr[A = A₀]`. -/
def ConnCorr {k : ℕ} (f : Omega k → Omega k → ℝ) (A0 B0 : Omega k) : Prop :=
  (∀ B ∈ setX k A0, ∀ A ∈ setY k B0, 0 < f B A) ∧
    (∑ A ∈ setY k B0, f B0 A) / (∑ B ∈ setX k A0, ∑ A ∈ setY k B0, f B A) =
        (∑ B ∈ setX k A0, f B A0) / (∑ B ∈ setX k A0, ∑ A ∈ setY k B0, f B A) ∧
      (∑ A ∈ setY k B0, f B0 A) / (∑ B ∈ setX k A0, ∑ A ∈ setY k B0, f B A) *
          ((∑ B ∈ setX k A0, f B A0) / (∑ B ∈ setX k A0, ∑ A ∈ setY k B0, f B A)) <
        f B0 A0 / (∑ B ∈ setX k A0, ∑ A ∈ setY k B0, f B A)

/-- The total weight of one connector from a block of value `σv` to a block of value `σw`, Lemma 11 and
§3.2.2 (pp.9, 11; PDF pp.11, 13): `z_R` has label `B₀` if `σv = 1` and ranges over `X` if `σv = 0`; `z_L`
has label `A₀` if `σw = 0` and ranges over `Y` if `σw = 1`. Value `1` is `true`. -/
noncomputable def connDir {k : ℕ} (f : Omega k → Omega k → ℝ) (A0 B0 : Omega k) (σv σw : Bool) : ℝ :=
  ∑ B ∈ (if σv then {B0} else setX k A0), ∑ A ∈ (if σw then setY k B0 else {A0}), f B A

/-- The conclusion of Lemma 11, p.11 (PDF p.13): `b > 0`, `θ > 1`, and the two connectors between
two blocks, one in each direction, have total weight `b²` if the values are equal and `b²θ` otherwise. -/
def ConnAntiferro {k : ℕ} (f : Omega k → Omega k → ℝ) (A0 B0 : Omega k) (b θ : ℝ) : Prop :=
  0 < b ∧ 1 < θ ∧ ∀ σv σw : Bool,
    connDir f A0 B0 σv σw * connDir f A0 B0 σw σv = if σv = σw then b ^ 2 else b ^ 2 * θ

end BipColorHard


