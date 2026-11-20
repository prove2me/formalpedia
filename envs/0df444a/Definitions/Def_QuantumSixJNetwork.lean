-- Prove2me | Definitions.Def_QuantumSixJNetwork
-- name    : QuantumSixJNetwork
-- status  : Definition
-- author  : @igor.kh
-- created : 2026-11-13T00:16:18.039208+00:00
-- url     : https://prove2.me/theorems/6ff0fe68-e6f9-40a0-8c0b-5c604545317b
-- title:
--   Quantum 6j categorical data and graphical networks
-- statement:
--   Let $K=\mathbb C(q)$ and let $\iota:\mathbb Q(q)\hookrightarrow K$ fix the indeterminate. The data are a $K$-linear preadditive monoidal category whose tensor product is additive and linear in each variable, labeled objects $V_n$ for $n\in\mathbb N$, an isomorphism $V_0\cong\mathbb1$, and exact self-pairings giving cups and caps satisfying both zigzag identities.
--
--   The category axioms are scalar endomorphisms of each labeled object with unique coefficient, vanishing morphisms between distinct labels, the admissible $\mathrm{SL}(2)$ fusion decompositions, and loop values $\Delta_n$. A vertex family chooses a morphism $V_a\otimes V_b\otimes V_c\to\mathbb1$ for each natural triple. Its other vertex forms, horizontally and vertically coupled networks $H,X$, reflections, and rung operators are defined by explicit compositions using cups and caps. Composition is read left to right, and tensor factors are ordered top to bottom.
--
--   The graphical tetrahedral network of equation (6) is
--   $$T(a,b,c,d;j,l)=X(a,d,c,b;j)\mathbin{\gg}H^R(a,d,c,b;l)$$
--   for nonnegative channels $j,l$, and zero if either channel is negative. The last channel is the inner rung. In Lean this is `Vertex.tet`; it is an endomorphism of the tensor unit.
--
--   `VertexNormalized` assumes only the theta value and cyclicity of the trivalent vertex. The separate assumption `TetSeed` specifies the last-slot-$2$ initial values
--   $$T(a,b,c,d;j,2)=\iota\!\left(\operatorname{Tet}^{\mathrm{sum}}(a,b,c,d;j,2)\right)\mathrm{id}_{\mathbb1}.$$
--   These values are seed data for the solution of the recurrence and also input to its derivation, rather than vertex-normalization conditions. `TetSeed.tet_two` states the displayed equality for all natural external labels and natural $j$. No all-channel numerical evaluation, second initial evaluation, braiding or general tetrahedral rotation is assumed.
--
--   Kauffman–Lins is the standard reference for diagrammatic notation. Etingof–Ostrik and Chen provide accessible online accounts grounding the category axioms. The relevant representation theory of $\mathrm{su}_q(2)$ is not available in Mathlib; constructing it is outside this scope, so the properties required by the argument are assumed explicitly rather than supplied by a constructed category.
-- source:
--   I. Khavkine, Recurrence relation for the 6j-symbol of su_q(2) as a symmetric eigenvalue problem, International Journal of Geometric Methods in Modern Physics (2015); https://doi.org/10.1142/S0219887815501170; https://arxiv.org/abs/1009.2261. Eq. (6), graphical Tet; Eqs. (23), (24). Notation: Kauffman–Lins (1994), https://press.princeton.edu/books/paperback/9780691036403/temperley-lieb-recoupling-theory-and-invariants-of-3-manifolds. Category properties: Etingof–Ostrik, https://arxiv.org/abs/math/0302130, §2; Chen, https://arxiv.org/abs/1502.06845.

import Definitions.Def_QuantumSixJScalar

/-!
Diagram conventions for the doc comments below.

* Morphisms compose left to right; each vertical bar `|` is one composition,
  with `≫` or `⊗≫` written above it. A `⊗≫` bar only regroups strands
  (associators and unitors) and draws nothing.
* Tensor factors are stacked top to bottom, so in `X ◁ f` the whisker `X` is
  the top strand and in `f ▷ X` it is the bottom strand.
* Strands carry twice-spin labels: `a` stands for `V a`. A strand ends at the
  left edge if it is an input and at the right edge if it is an output.
* A cup `(` opens two strands of equal label; a cap `)` closes them.
-/

noncomputable section
namespace QuantumSixJ.Network
open CategoryTheory MonoidalCategory
open QuantumSixJ
open scoped BigOperators

universe v u

/-- The scalar field `ℂ(q)`. -/
abbrev K := RatFunc ℂ

/-- The coefficient embedding `ℚ(q) → ℂ(q)`, fixing `q`. -/
def ι : Scalar →+* K :=
  RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap ℚ ℂ))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective _ (algebraMap ℚ ℂ).injective))

open scoped Classical in
/-- The labels `c ≤ a + b` such that `(a, b, c)` is admissible. -/
def fusionRange (a b : ℕ) : Finset ℕ :=
  (Finset.range (a + b + 1)).filter fun c => Admissible (a : ℤ) b c

variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear K C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear K C]

/-- Label data: labelled objects, each self-dual through one cup and one cap
satisfying both zigzag identities. -/
structure SuQ2Data where
  V : ℕ → C
  unitIso : V 0 ≅ 𝟙_ C
  pairing : ∀ a, ExactPairing (V a) (V a)

variable {C}

namespace SuQ2Data

variable (S : SuQ2Data C)

/-- The cup `𝟙 ⟶ a ⊗ a`.
```text
  .--- a
 (
  `--- a
```
-/
def cup (a : ℕ) : 𝟙_ C ⟶ S.V a ⊗ S.V a := (S.pairing a).coevaluation'

/-- The cap `a ⊗ a ⟶ 𝟙`.
```text
  a ---.
        )
  a ---'
```
-/
def cap (a : ℕ) : S.V a ⊗ S.V a ⟶ 𝟙_ C := (S.pairing a).evaluation'

end SuQ2Data

/-- Category axioms: simplicity of the labelled objects, the `SL(2)` fusion
rules, and the loop values. -/
structure SuQ2Axioms (S : SuQ2Data C) : Prop where
  simple : ∀ a (f : S.V a ⟶ S.V a), ∃! s : K, f = s • 𝟙 (S.V a)
  disjoint : ∀ a b, a ≠ b → ∀ f : S.V a ⟶ S.V b, f = 0
  /-- Fusion: maps `i c` and `p c` with, for `c ∈ fusionRange a b`,
  `i c ≫ p c = 𝟙 (V c)`, and `∑ c ∈ fusionRange a b, p c ≫ i c = 𝟙 (V a ⊗ V b)`.
  ```text
                    ≫                                         ≫
          +-----+       |  +-----+                 +-----+       |  +-----+
          |     |-- a --|--|     |         a ------|     |       |  |     |------ a
  c ------| i c |       |  | p c |------ c         | p c |-- c --|--| i c |
          |     |-- b --|--|     |         b ------|     |       |  |     |------ b
          +-----+       |  +-----+                 +-----+       |  +-----+

          i c ≫ p c  =  c ----- c          sum over c of  p c ≫ i c  =  identity on a, b
  ```
  -/
  fusion : ∀ a b, ∃ (i : ∀ c, S.V c ⟶ S.V a ⊗ S.V b) (p : ∀ c, S.V a ⊗ S.V b ⟶ S.V c),
    (∀ c ∈ fusionRange a b, i c ≫ p c = 𝟙 (S.V c)) ∧
      ∑ c ∈ fusionRange a b, p c ≫ i c = 𝟙 (S.V a ⊗ S.V b)
  /-- The loop `cup a ≫ cap a` is the scalar `Δ a`.
  ```text
               ≫
     .--- a ---|--- a ---.
    (          |          )      =  ι (Δ a) • 𝟙
     `--- a ---|--- a ---'
  ```
  -/
  loop : ∀ a, S.cup a ≫ S.cap a = ι (Δ a) • 𝟙 (𝟙_ C)

/-- Vertex data: a chosen 3-vertex for each triple of labels.
`vertex a b c` has inputs `a, b, c`, top to bottom, and no outputs.
```text
       +-------+
  a ---|       |
  b ---|vertex |
  c ---| a b c |
       +-------+
```
-/
structure Vertex (S : SuQ2Data C) where
  vertex : ∀ a b c, S.V a ⊗ S.V b ⊗ S.V c ⟶ 𝟙_ C

namespace Vertex

variable {S : SuQ2Data C} (W : Vertex S)

/-- Move the first leg of a 3-leg covector to the last place.
The leg that `f` takes first (top) is carried around the right end and becomes
the last (bottom) input; the picture has no crossings.
```text
               ⊗≫                      ⊗≫                     ⊗≫
     𝟙         |    cup a ▷ (b⊗c⊗a)    |     a ◁ (f ▷ a)      |  cap a
               |                       |                      |
               |    .------- a --------|--------- a ----------|---.
               |   (                   |                      |    \
               |    `------- a --------|------ a ---+---+     |     \
               |                       |            |   |     |      |
 b ----------- | ----------- b --------|------ b ---| f |     |      |
               |                       |            |   |     |      |
 c ----------- | ----------- c --------|------ c ---+---+     |      |
               |                       |                      |     /
 a ----------- | ----------- a --------|--------- a ----------|----'
```
-/
def rotate {a b c : ℕ} (f : S.V a ⊗ S.V b ⊗ S.V c ⟶ 𝟙_ C) :
    S.V b ⊗ S.V c ⊗ S.V a ⟶ 𝟙_ C :=
  𝟙 _ ⊗≫ (S.cup a ▷ (S.V b ⊗ S.V c ⊗ S.V a)) ⊗≫
    (S.V a ◁ (f ▷ S.V a)) ⊗≫ S.cap a

/-- `I^{abc}`: the vertex `I_{cba}` with all three legs bent, by nested cups.
```text
           ⊗≫        ⊗≫          ⊗≫            ⊗≫
     (1)   |   (2)   |    (3)    |     (4)     |  (5)
           |         |           |  +-------+  |
  .-- c ---|--- c ---|---- c ----|--|       |  |
 (         |         |           |  |       |  |
  |        |  .- b --|---- b ----|--| c b a |  |
  |        | (       |           |  |       |  |
  |        |  |      |  .- a ----|--|       |  |
  |        |  |      | (         |  +-------+  |
  |        |  |      |  `- a ----|-------------|---- a
  |        |  `- b --|---- b ----|-------------|---- b
  |        |         |           |             |
  `-- c ---|--- c ---|---- c ----|-------------|---- c

  (1) cup c                 (2) c ◁ (cup b ▷ c)    (3) c ◁ ((b ◁ (cup a ▷ b)) ▷ c)
  (4) vertex c b a ▷ (a ⊗ b ⊗ c)                   (5) 𝟙
```
-/
def vertexUp (a b c : ℕ) : 𝟙_ C ⟶ S.V a ⊗ S.V b ⊗ S.V c :=
  S.cup c ⊗≫ (S.V c ◁ (S.cup b ▷ S.V c)) ⊗≫
    (S.V c ◁ ((S.V b ◁ (S.cup a ▷ S.V b)) ▷ S.V c)) ⊗≫
    (W.vertex c b a ▷ (S.V a ⊗ S.V b ⊗ S.V c)) ⊗≫ 𝟙 _

/-- `I_l^{ab} : V_l → V_a ⊗ V_b`: the vertex `I_{bal}` with its first two legs bent.
```text
         ⊗≫          ⊗≫           ⊗≫          ⊗≫
   (1)   |    (2)    |    (3)     |    (4)    |  (5)
         |           |            |           |
         |  .-- a ---|---- a -----|----- a ---|---- a
         | (         |            |           |
         |  |        |  .-- b ----|----- b ---|---- b
         |  |        | (          |  +-----+  |
         |  |        |  `-- b ----|--|     |  |
         |  |        |            |  |     |  |
         |  `-- a ---|---- a -----|--|b a l|  |
         |           |            |  |     |  |
  l -----|---- l ----|---- l -----|--|     |  |
         |           |            |  +-----+  |

  (1) 𝟙    (2) cup a ▷ l    (3) a ◁ ((cup b ▷ a) ▷ l)
  (4) a ◁ b ◁ vertex b a l    (5) 𝟙
```
-/
def split (l a b : ℕ) : S.V l ⟶ S.V a ⊗ S.V b :=
  𝟙 _ ⊗≫ (S.cup a ▷ S.V l) ⊗≫ (S.V a ◁ ((S.cup b ▷ S.V a) ▷ S.V l)) ⊗≫
    (S.V a ◁ S.V b ◁ W.vertex b a l) ⊗≫ 𝟙 _

/-- `I_{ab}^l : V_a ⊗ V_b → V_l`: the vertex `I_{abl}` with its last leg bent.
```text
         ⊗≫        ⊗≫          ⊗≫
   (1)   |   (2)   |    (3)    |  (4)
         |         |  +-----+  |
  a -----|--- a ---|--|     |  |
         |         |  |     |  |
  b -----|--- b ---|--|a b l|  |
         |         |  |     |  |
         |  .- l --|--|     |  |
         | (       |  +-----+  |
         |  `- l --|---- l ----|---- l

  (1) 𝟙    (2) (a ⊗ b) ◁ cup l    (3) vertex a b l ▷ l    (4) 𝟙
```
-/
def fuse (a b l : ℕ) : S.V a ⊗ S.V b ⟶ S.V l :=
  𝟙 _ ⊗≫ ((S.V a ⊗ S.V b) ◁ S.cup l) ⊗≫ (W.vertex a b l ▷ S.V l) ⊗≫ 𝟙 _

/-- The vertical state `X_l`.
```text
            ⊗≫            ⊗≫
    (1)     |     (2)     |  (3)
            |  +-------+  |
  .--- l ---|--| split |--|--- a
 (          |  | l a b |  |
  |         |  |       |--|--- b
  |         |  +-------+  |
  |         |  +-------+  |
  |         |  |       |--|--- c
  |         |  | split |  |
  `--- l ---|--| l c d |--|--- d
            |  +-------+  |

  (1) cup l    (2) split l a b ⊗ₘ split l c d    (3) 𝟙
```
-/
def X (a b c d l : ℕ) : 𝟙_ C ⟶ S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d :=
  S.cup l ⊗≫ (W.split l a b ⊗ₘ W.split l c d) ⊗≫ 𝟙 _

/-- The reflected vertical state `X_l^R`.
```text
         ⊗≫                 ⊗≫
   (1)   |       (2)        |   (3)
         |   +---------+    |
  a -----|---|  fuse   |    |
         |   |  a b l  |-l--|---.
  b -----|---|         |    |    \
         |   +---------+    |     |
         |   +---------+    |     |
  c -----|---|  fuse   |    |    /
         |   |  c d l  |-l--|---'
  d -----|---|         |    |
         |   +---------+    |

  (1) 𝟙    (2) fuse a b l ⊗ₘ fuse c d l    (3) cap l
```
-/
def Xcov (a b c d l : ℕ) : S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d ⟶ 𝟙_ C :=
  𝟙 _ ⊗≫ (W.fuse a b l ⊗ₘ W.fuse c d l) ⊗≫ S.cap l

/-- The horizontal state `H_j`.
```text
                    ⊗≫                 ⊗≫
         (1)        |       (2)        |  (3)
  +----------+      |                  |
  |          |-- a -|------- a --------|--- a
  | vertexUp |      |   +---------+    |
  |  a j d   |-- j -|---|  split  |----|--- b
  |          |      |   |  j b c  |    |
  |          |      |   |         |----|--- c
  |          |      |   +---------+    |
  |          |-- d -|------- d --------|--- d
  +----------+      |                  |

  (1) vertexUp a j d    (2) a ◁ (split j b c ▷ d)    (3) 𝟙
```
-/
def H (a b c d j : ℕ) : 𝟙_ C ⟶ S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d :=
  W.vertexUp a j d ⊗≫ (S.V a ◁ (W.split j b c ▷ S.V d)) ⊗≫ 𝟙 _

/-- The reflected horizontal state `H_j^R`.
```text
         ⊗≫                 ⊗≫
   (1)   |       (2)        |      (3)
         |                  |  +-------+
  a -----|------- a --------|--|       |
         |   +---------+    |  |       |
  b -----|---|  fuse   |    |  |vertex |
         |   |  b c j  |-j--|--| a j d |
  c -----|---|         |    |  |       |
         |   +---------+    |  |       |
  d -----|------- d --------|--|       |
         |                  |  +-------+

  (1) 𝟙    (2) a ◁ (fuse b c j ▷ d)    (3) vertex a j d
```
-/
def Hcov (a b c d j : ℕ) : S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d ⟶ 𝟙_ C :=
  𝟙 _ ⊗≫ (S.V a ◁ (W.fuse b c j ▷ S.V d)) ⊗≫ W.vertex a j d

/-- The operator `K2` on `V_a ⊗ V_b`, with the two dotted vertices of the paper:
`[a][b]` times a rung of label `2` from the `a` strand to the `b` strand.
```text
                   ⊗≫
          (1)      |       (2)
       +-------+   |
  a ---| split |---|------- a -------- a
       | a a 2 |   |
       |       |-2-|---+-------+
       +-------+   |   | fuse  |
  b ---------------|---| 2 b b |------ b
                   |   +-------+

  ι ([a] [b]) • ( (1) ⊗≫ (2) ),    (1) split a a 2 ▷ b    (2) a ◁ fuse 2 b b
```
-/
def K2 (a b : ℕ) : S.V a ⊗ S.V b ⟶ S.V a ⊗ S.V b :=
  ι (⟬(a : ℤ)⟭ * ⟬(b : ℤ)⟭) •
    ((W.split a a 2 ▷ S.V b) ⊗≫ (S.V a ◁ W.fuse 2 b b))

/-- The operator `L`: `K2` acting on the first two of the four legs.
```text
         ⊗≫             ⊗≫
   (1)   |      (2)     |  (3)
         |   +-------+  |
  a -----|---|       |--|--- a
         |   |  K2   |  |
  b -----|---|  a b  |--|--- b
         |   +-------+  |
  c -----|------ c -----|--- c
  d -----|------ d -----|--- d

  (1) 𝟙    (2) K2 a b ▷ (c ⊗ d)    (3) 𝟙
```
-/
def Kop (a b c d : ℕ) :
    S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d ⟶ S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d :=
  𝟙 _ ⊗≫ (W.K2 a b ▷ (S.V c ⊗ S.V d)) ⊗≫ 𝟙 _

open scoped Classical in
/-- The graphical tetrahedral network of equation (6).
Composition is read left to right; l is the inner rung.
```text
                 ≫
  +---------+    |   +---------+
  |         |-a--|---|         |
  |   X_j   |-d--|---|  H_l^R  |
  | a d c b |-c--|---| a d c b |
  |         |-b--|---|         |
  +---------+    |   +---------+

  X a d c b j   ≫   Hcov a d c b l
```
The value is zero if either channel is negative.
-/
def tet (a b c d : ℕ) (j l : ℤ) : 𝟙_ C ⟶ 𝟙_ C :=
  if 0 ≤ j ∧ 0 ≤ l then W.X a d c b j.toNat ≫ W.Hcov a d c b l.toNat else 0

end Vertex

/-- Vertex normalization: the normalization of the chosen vertex. -/
structure VertexNormalized {S : SuQ2Data C} (W : Vertex S) : Prop where
  /-- The theta network.
  ```text
                     ≫
    +----------+     |   +--------+
    |          |- a -|---|        |
    | vertexUp |- b -|---| vertex |      =  ι (θ a b c) • 𝟙
    |  a b c   |- c -|---| a b c  |
    +----------+     |   +--------+
  ```
  -/
  theta : ∀ a b c : ℕ, W.vertexUp a b c ≫ W.vertex a b c = ι (θ a b c) • 𝟙 (𝟙_ C)
  /-- Cyclicity: the `rotate` diagram with `f = vertex a b c` equals `vertex b c a`. -/
  cyclic : ∀ a b c : ℕ, Vertex.rotate (W.vertex a b c) = W.vertex b c a

/-- Seed data for the graphical tetrahedral recurrence: its values at inner
rung `l = 2`. These initial values also serve as input to the derivation of
the recurrence, separately from vertex normalization.
-/
structure TetSeed {S : SuQ2Data C} (W : Vertex S) : Prop where
  /-- The `tet` diagram with inner rung `l = 2` equals the Appendix sum `tetSum`.
  The scalar arguments remain `a b c d j 2`; only the network presentation
  permutes the boundary labels to `a d c b`.
  -/
  tet_two : ∀ a b c d j : ℕ, W.tet a b c d j 2 = ι (tetSum a b c d j 2) • 𝟙 (𝟙_ C)

end QuantumSixJ.Network
end


