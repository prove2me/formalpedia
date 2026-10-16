-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_BlockObstruction__RealL1Renorming
-- name    : OAI_Analysis_LipschitzFree_BlockObstruction__RealL1Renorming
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T12:31:07.373695+00:00
-- url     : https://prove2.me/theorems/b167feab-f429-43f1-a638-3b709b2870b4
-- title:
--   The metric block $\mathcal{M}_p$: colored Cayley graph sequence, label anchors, base point and anchor set
-- statement:
--   Fix $p\in\mathbb{N}$ and define the natural numbers
--   $$
--   L=10p,\quad R=3L,\quad K=10p\,(R+1),\quad D=K+2L+5,\quad B=4R+D,\quad V=1+4pB,
--   $$
--   $$
--   g=20V+2,\quad \Delta=2g,\quad Q=\Delta^{2L+1},\quad H=\Delta^{D+1},\quad \kappa=2\Delta QH+1 .
--   $$
--   In closed form $R=30p$, $D=300p^2+30p+5$ and $B=300p^2+150p+5$.
--
--   **The colored graph.** Let $\Sigma_p=\{0,\dots,g-1\}$ be a set of $g$ generators and $C_p=\{0,\dots,\kappa-1\}$ a set of $\kappa$ colors. For $N\in\mathbb{N}$ let $\Gamma_N$ be the finite group of permutations of the ball of radius $N$ (reduced word length at most $N$) in the free group $F(\Sigma_p)$, and let $\rho_N\colon F(\Sigma_p)\to\Gamma_N$ be the homomorphism sending each generator $a$ to a fixed permutation of the ball that agrees with $h\mapsto a\,h$ wherever $a\,h$ stays in the ball. The vertex set $X_p$ consists of all triples $(N,c,x)$ with $N\in\mathbb{N}$, $c\colon\Gamma_N\to C_p$ and $x\in\Gamma_N$. The ports are the pairs $(a,\epsilon)\in\Sigma_p\times\{+1,-1\}$; the port $(a,\epsilon)$ moves $(N,c,x)$ to $(N,c,x\,\rho_N(a)^{\epsilon})$, and its reverse is $(a,-\epsilon)$. The color of a vertex is $\chi_p(N,c,x)=c(x)$.
--
--   **The block.** For a vertex $v$ and a color $i$ let $\ell_i(v)\in\{0,\dots,D\}$ be the least $n$ such that $n=D$ or some port word of length $n$ leads from $v$ to a vertex of color $i$, and put $\ell(v)=(\ell_i(v))_{i\in C_p}$. The anchors are the label vectors that occur, $\mathcal{A}_p=\{\ell(v):v\in X_p\}$, a finite subset of $\{0,\dots,D\}^{C_p}$. The points of the block are $\mathcal{M}_p=X_p\sqcup\mathcal{A}_p$, and distinct points get the weights
--   $$
--   \omega(v,v')=\begin{cases}1 & v'=v\cdot e\ \text{for some port } e,\\ 4R+D & \text{otherwise,}\end{cases}\qquad
--   \omega(v,a)=\omega(a,v)=\begin{cases}R & a=\ell(v),\\ 4R+D & \text{otherwise,}\end{cases}\qquad
--   \omega(a,b)=2R+\max_{i\in C_p}|a_i-b_i|
--   $$
--   for vertices $v,v'$ and anchors $a,b$ (and $\omega(u,u)=0$). The distance $d(u,u')$ is the least total weight $\sum_{t=1}^{k}\omega(z_{t-1},z_t)$ of a chain $u=z_0,z_1,\dots,z_k=u'$ with $k\ge1$. When $R>0$, that is $p\ge1$, all weights between distinct points are positive and $d$ is an integer-valued metric.
--
--   The module defines:
--
--   1. **Alphabets.** The generator set $\Sigma_p$, the color set $C_p$ (nonempty), the port set $\Sigma_p\times\{+1,-1\}$ (nonempty) and the vertex set $X_p$. There are exactly $\Delta=2g$ ports and $\kappa$ colors.
--   2. **Graph and coloring.** The port graph on $X_p$ and the coloring $\chi_p$ described above.
--   3. **The block.** $\mathcal{M}_p=X_p\sqcup\mathcal{A}_p$ with cap $D$ and attachment radius $R$, carrying the metric $d$.
--   4. **Base point.** The base vertex $v_0=(0,\ \text{the constant coloring with color }0,\ \mathrm{id})$ and the base point $o_p=\ell(v_0)$, the anchor carrying the label of $v_0$, viewed as a point of $\mathcal{M}_p$.
--   5. **Anchor set.** The finite set $\mathcal{A}_p\subseteq\mathcal{M}_p$ of all anchor points; it contains $o_p$.
--   6. **Basic properties.** If $R>0$, distinct points satisfy $d(u,u')\ge1$, and $\mathcal{M}_p$ is infinite, since the vertices $(n,\ \text{constant coloring }0,\ \mathrm{id})$, $n\in\mathbb{N}$, are pairwise distinct.
--
--   For $p\ge1$, $(\mathcal{M}_p,o_p)$ is the pointed metric space behind the renorming of real $\ell^1$: it is countable, infinite and $1$-separated, and every distance is at most a single weight, hence at most $4R+D=B=300p^2+150p+5$. These facts make its Lipschitz-free space isomorphic to $\ell^1$, while the finite anchor set carries the obstruction showing that this free space fails the bounded approximation property with constant $p$.
--
--   **Formalization Note** The objects are `Generators p = Fin (generators p)`, `Colors p = Fin (colors p)`, `Ports p = Generators p × Bool`, `Vertices p`, `graph p`, `color p`, `Block p = MetricBlock.Point (graph p) (color p) (D p) (R p)`, `baseVertex p`, `base p` and `anchors p` (a `Finset (Block p)`); the parameters are `BlockParameters.L`, `R`, `K`, `D`, `B`, `V`, `generators`, `degree` ($=\Delta$), `Q`, `H` and `colors` ($=\kappa$). The metric instance on `Block p`, the lemma `separation` and the instance `infinite_block` are stated under the hypothesis `Fact (0 < R p)`. The lemmas `card_ports`, `nat_card_ports` and `nat_card_colors` are the cardinality identities of item 1.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/BlockObstruction.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/BlockObstruction.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RealL1Renorming mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Model__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Coefficients
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Words__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_AffineWeights__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_LabelBumps__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_ScalarTests__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_FiniteQuotients__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphGirth__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_ColorCounting__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphColoring__RealL1Renorming

namespace OAI

/-!
# Signed finite-rank obstruction on countable bounded metric blocks
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.BlockConstruction
open scoped Classical BigOperators
open BlockParameters

abbrev Generators (p : ℕ) := Fin (generators p)
abbrev Colors (p : ℕ) := Fin (colors p)
abbrev Ports (p : ℕ) := Generators p × Bool
abbrev Vertices (p : ℕ) := GraphProducer.Vertex (Generators p) (Colors p)

instance (p : ℕ) : Nonempty (Colors p) := ⟨⟨0,colors_pos p⟩⟩
instance (p : ℕ) : Nonempty (Ports p) := ⟨⟨⟨0,by dsimp [generators]; omega⟩,true⟩⟩

def graph (p : ℕ) := GraphProducer.sequenceGraph (Generators p) (Colors p)
def color (p : ℕ) := GraphProducer.sequenceColor (Generators p) (Colors p)
abbrev Block (p : ℕ) := MetricBlock.Point (graph p) (color p) (D p) (R p)

def baseVertex (p : ℕ) : Vertices p := ⟨0,(fun _ => ⟨0,colors_pos p⟩),1⟩

def base (p : ℕ) : Block p := MetricBlock.ofAnchor (graph p) (color p) (D p) (R p)
  (MetricBlock.anchorOf (graph p) (color p) (D p) (baseVertex p))

def anchors (p : ℕ) : Finset (Block p) := Finset.univ.image
  (MetricBlock.ofAnchor (graph p) (color p) (D p) (R p))

@[simp] theorem card_ports (p : ℕ) : Fintype.card (Ports p) = degree p := by
  simp [Ports,degree,Nat.mul_comm]

@[simp] theorem nat_card_ports (p : ℕ) : Nat.card (Ports p) = degree p := by
  simp only [Nat.card_eq_fintype_card,card_ports]

@[simp] theorem nat_card_colors (p : ℕ) : Nat.card (Colors p) = colors p := Nat.card_fin _

variable (p : ℕ) [Fact (0 < R p)]

theorem separation (x y : Block p) (h : x ≠ y) : 1 ≤ dist x y :=
  MetricBlock.separated (graph p) (color p) (D p) (R p) h

instance infinite_block : Infinite (Block p) := by
  apply Infinite.of_injective (fun n : ℕ =>
    MetricBlock.ofVertex (graph p) (color p) (D p) (R p)
      (⟨n,(fun _ => ⟨0,colors_pos p⟩),1⟩ : Vertices p))
  intro n m h
  have h' := Sum.inl.inj h
  exact congrArg Sigma.fst h'

end DiscreteFree.BlockConstruction

namespace DiscreteFree

end DiscreteFree
end

end

end OAI


