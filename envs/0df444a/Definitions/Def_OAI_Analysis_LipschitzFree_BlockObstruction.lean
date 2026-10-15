-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_BlockObstruction
-- name    : OAI_Analysis_LipschitzFree_BlockObstruction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:33:03.081594+00:00
-- url     : https://prove2.me/theorems/8c0ca9f8-7360-4a75-abf7-33352086d23c
-- title:
--   The metric block $\mathcal{M}_p$ over the colored graph sequence, with its base point and anchor set
-- statement:
--   Fix $p\in\mathbb{N}$ and the natural-number parameters
--   $$
--   L=10p,\quad R=3L,\quad K=10p(R+1),\quad D=K+2L+5,\quad B=4R+D,\quad V=1+4pB,
--   $$
--   $$
--   g=20V+2,\quad \Delta=2g,\quad Q=\Delta^{2L+1},\quad H=\Delta^{D+1},\quad \kappa=2\Delta QH+1 .
--   $$
--   Let $\Sigma_p=\{0,\dots,g-1\}$ be a set of $g$ generators and $C_p=\{0,\dots,\kappa-1\}$ a set of $\kappa$ colors. Let $(X_p,\chi_p)$ be the countable colored port graph built from them: its vertices are triples $(N,c,x)$ with $N\in\mathbb{N}$, $x$ in the finite group $\Gamma_N$ of permutations of the radius-$N$ ball of the free group on $\Sigma_p$, and $c\colon\Gamma_N\to C_p$ a coloring; a port $(a,\epsilon)\in \Sigma_p\times\{+1,-1\}$ moves $(N,c,x)$ to $(N,c,x\rho_N(a)^{\epsilon})$, where $\rho_N$ is a fixed homomorphism from the free group to $\Gamma_N$ that agrees with left multiplication on the ball where possible, and the vertex color is $\chi_p(N,c,x)=c(x)$.
--
--   The metric block over this graph uses the cap $D$ and the attachment radius $R$: for a vertex $v$ and a color $i$, the capped label $\ell_i(v)\in\{0,\dots,D\}$ is the least $n$ such that $n=D$ or some port word of length $n$ leads from $v$ to a vertex of color $i$, and $\ell(v)=(\ell_i(v))_{i}$ is the label vector of $v$. The anchors are the label vectors that actually occur, $\mathcal{A}_p=\{\ell(v)\}$, a finite set. The points of the block are the vertices and the anchors, $\mathcal{M}_p=X_p\sqcup\mathcal{A}_p$, and the weight of a pair of distinct points is
--   $$
--   \omega(v,v')=\begin{cases}1 & v'=v\cdot e\ \text{for some port } e,\\ 4R+D & \text{otherwise,}\end{cases}\qquad
--   \omega(v,a)=\omega(a,v)=\begin{cases}R & a=\ell(v),\\ 4R+D & \text{otherwise,}\end{cases}\qquad
--   \omega(a,b)=2R+\max_{i}|a_i-b_i|
--   $$
--   for vertices $v,v'$ and anchors $a,b$. The distance $d(u,u')$ is the minimum total weight $\sum_t\omega(z_{t-1},z_t)$ of a finite chain $u=z_0,z_1,\dots,z_k=u'$ $(k\ge1)$, an integer-valued metric (well defined since $R>0$, i.e. $p\ge1$).
--
--   The module defines:
--
--   1. **Alphabets.** The generator set $\Sigma_p$, the color set $C_p$, the port set $\Sigma_p\times\{+1,-1\}$ and the vertex set $X_p$; there are exactly $\Delta=2g$ ports and $\kappa$ colors.
--   2. **Graph and coloring.** The sequence port graph on $X_p$ and its coloring $\chi_p$ described above.
--   3. **The block.** $\mathcal{M}_p=X_p\sqcup\mathcal{A}_p$ with the metric $d$ (cap $D$, radius $R$).
--   4. **Base point.** The base vertex $v_0=(0,\text{constant coloring }0,\mathrm{id})$ and the base point $o_p=\ell(v_0)$, viewed as an anchor point of $\mathcal{M}_p$.
--   5. **Anchor set.** The finite set $\mathcal{A}_p\subseteq\mathcal{M}_p$ of all anchor points; it contains $o_p$.
--   6. **Basic properties.** When $R>0$, distinct points of $\mathcal{M}_p$ satisfy $d(u,u')\ge1$; and $\mathcal{M}_p$ is infinite (the vertices $(n,\text{constant coloring }0,\mathrm{id})$, $n\in\mathbb{N}$, are distinct).
--
--   For $p\ge1$, the pointed space $(\mathcal{M}_p,o_p)$ together with the finite set $\mathcal{A}_p$ is the witness for the block statement of the mission: $\mathcal{M}_p$ is countable, uniformly $1$-separated, of diameter at most $B=300p^2+150p+5$, and every finite-rank operator $T$ on $\mathcal{F}(\mathcal{M}_p,o_p)$ with $\|T\|\le p$ satisfies $\|T\delta_a-\delta_a\|\ge\tfrac12$ for some anchor $a\in\mathcal{A}_p$.
--
--   **Formalization Note** The objects are `Generators p = Fin (generators p)`, `Colors p = Fin (colors p)`, `Ports p = Generators p × Bool`, `Vertices p`, `graph p`, `color p`, `Block p = MetricBlock.Point (graph p) (color p) (D p) (R p)`, `baseVertex p`, `base p` and `anchors p`; the parameters are `BlockParameters.L p`, `R p`, `K p`, `D p`, `B p`, `V p`, `generators p`, `degree p` $=\Delta$, `Q p`, `H p`, `colors p` $=\kappa$. The metric instance on `Block p` and the lemma `separation` require the hypothesis `Fact (0 < R p)`. The lemmas `card_ports`, `nat_card_ports`, `nat_card_colors` are the cardinality identities of item 1 and `infinite_block` is the infinitude instance.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/BlockObstruction.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/BlockObstruction.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DiscreteLipschitzFree mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
import Definitions.Def_OAI_Analysis_LipschitzFree_Words
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates
import Definitions.Def_OAI_Analysis_LipschitzFree_AffineWeights
import Definitions.Def_OAI_Analysis_LipschitzFree_LabelBumps
import Definitions.Def_OAI_Analysis_LipschitzFree_ScalarTests
import Definitions.Def_OAI_Analysis_LipschitzFree_FiniteQuotients
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphGirth
import Definitions.Def_OAI_Analysis_LipschitzFree_ColorCounting
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphColoring

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


