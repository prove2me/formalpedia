-- Prove2me | Definitions.Def_OAI_RepresentationTheory_Saxl_BandSupport
-- name    : OAI_RepresentationTheory_Saxl_BandSupport
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:12:18.805329+00:00
-- url     : https://prove2.me/theorems/7fc34ffb-5aa4-45d0-920e-1781e3fd2fec
-- title:
--   Two-layer band vectors, alphabet subrepresentations and letter-shifted staircase vectors
-- statement:
--   Vectors and maps attached to the band of a staircase, in the pair-letter word spaces that carry tensor squares.
--
--   For $n,d\in\mathbb{N}$ write $[n]=\{0,1,\dots,n-1\}$ and let $M_{n,d}$ be the complex vector space of functions $x:[d]^{[n]}\to\mathbb{C}$ on words $w:[n]\to[d]$ (positions $[n]$, letters $[d]$), with indicator vectors $\delta_w$; the symmetric group $\mathfrak S_n$ acts by $(g\cdot x)(w)=x(w\circ g)$, so that $g\cdot\delta_w=\delta_{w\circ g^{-1}}$. A letter of $[d^2]$ is identified with a pair $(a,b)\in[d]\times[d]$ through $(a,b)\leftrightarrow ad+b$, so a word $w$ over $[d^2]$ is a pair $(w^{(1)},w^{(2)})$ of words over $[d]$, and $M_{n,d}\otimes M_{n,d}\cong M_{n,d^2}$ via $(x\otimes y)(w)=x(w^{(1)})\,y(w^{(2)})$. A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both indexed from $0$) closed under moving up or to the left; $|\mu|$ is its number of cells. A tableau of shape $\mu$ on the positions $[n]$ is a bijection $t:[n]\to\mu$; its column group $C_t\le\mathfrak S_n$ consists of the permutations $g$ such that $t(g(q))$ and $t(q)$ lie in the same column for every position $q$. The polytabloid of $t$ is $e_t=\sum_{g\in C_t}\operatorname{sgn}(g)\,\delta_{r_t\circ g^{-1}}$, where $r_t(q)$ is the row of $t(q)$.
--
--   The staircase of size $m$ is $\delta_m=\{(i,j)\in\mathbb{N}^2: i+j<m\}$; it has $m$ rows, so its row letters are $[m]$. It carries a fixed (canonical) tableau $t_m$, and $t_m^*$ denotes $t_m$ followed by the transposition $(i,j)\mapsto(j,i)$, again a tableau of $\delta_m$. For $h,s\in\mathbb{N}$ the band of $\delta_{h+s}$ consists of its cells with $h\le i+j<h+s$; let $b=b(h,s)$ be the number of positions $q$ with $t_{h+s}(q)$ in the band, these positions being enumerated by $[b]$ through a fixed bijection. The two band layers are
--   $$
--   \beta^{\mathrm{row}}_{h,s}=\sum_{g\in R}\operatorname{sgn}(g)\,\delta_{\alpha\circ g^{-1}},\qquad \beta^{\mathrm{col}}_{h,s}=\sum_{g\in C}\operatorname{sgn}(g)\,\delta_{\gamma\circ g^{-1}}\qquad\text{in } M_{b,h+s},
--   $$
--   where $R$ (resp. $C$) is the group of permutations $g$ of $[b]$ such that the band cells at $j$ and $g(j)$ lie in the same row (resp. column), and $\alpha$ (resp. $\gamma$) labels a band cell $(i,j)$ by its offset inside the band part of its row, $j-\max(h-i,0)$ (resp. of its column, $i-\max(h-j,0)$).
--
--   1. **Two-band vector.** $\beta_{h,s}=\beta^{\mathrm{row}}_{h,s}\otimes\beta^{\mathrm{col}}_{h,s}\in M_{b,(h+s)^2}$.
--
--   2. **Low pair letters.** $\lambda_h:[4]\to[h+2]\times[h+2]$ sends $a=2a_1+a_2$ (with $a_1,a_2\in\{0,1\}$) to the pair letter $(a_1,a_2)$; it embeds the four pairs of the two lowest row letters into the pair alphabet of $\delta_{h+2}$.
--
--   3. **Alphabet subrepresentation.** For a set $A\subseteq[d]$ of letters,
--   $$
--   M^{A}_{n,d}=\{x\in M_{n,d}:\ x(w)=0\ \text{whenever } w(i)\notin A \text{ for some } i\},
--   $$
--   the vectors supported on words over $A$; it is an $\mathfrak S_n$-subrepresentation of $M_{n,d}$.
--
--   4. **Pair lift.** For $\varphi:[d]\to[D]$, the $\mathfrak S_n$-intertwiner $M_{n,d^2}\to M_{n,D^2}$ sending $\delta_u$ to $\delta_{(\varphi\times\varphi)\circ u}$, i.e. $x\mapsto\big(w\mapsto\sum_{u:\,(\varphi\times\varphi)\circ u=w}x(u)\big)$; under the identification above it is $L_\varphi\otimes L_\varphi$ with $L_\varphi(\delta_a)=\delta_{\varphi\circ a}$.
--
--   5. **Shifted staircase vector.** With the staircase tensor vector $\Omega_h=e_{t_h^*}\otimes e_{t_h}\in M_{|\delta_h|,h^2}$, the vector $\Omega_h^{+s}\in M_{|\delta_h|,(h+s)^2}$ is the image of $\Omega_h$ under the pair lift of $a\mapsto a+s$, $[h]\to[h+s]$: every row letter in both components is raised by $s$.
--
--   When the staircase of size $h+s$ is cut along the band, the projection of $\Omega_{h+s}$ onto the words whose two letters are, at each position, both at least $s$ or both below $s$ is the position product of $\Omega_h^{+s}$ on the remaining positions (the cells with $i+j<h$, identified with the positions of $\delta_h$) and of $\beta_{h,s}$ on the band positions. The alphabet subrepresentations, the pair lift and the low pair letters are used to compare supports and to carry constituents of the smaller staircase module and of a four-letter path model into the corresponding cyclic modules.
--
--   **Formalization Note** The definitions are `stairBandWord h s` (the image of `bandRowWord h s ⊗ₜ bandColumnWord h s` under `wordTensor`), `lowPairLetter h`, `alphabetSub n d A`, `pairLift φ` and `shiftedStairWord h s = pairLift (highLetter h s) (staircaseWord h)`. The band positions are the right summand of `cutPositions h s` and $b$ is `bandSize h s`. The row-letter alphabet of $\delta_m$ appears as `Fin ((staircase m).colLen 0)`, whose size is $m$; the offsets $\alpha,\gamma$ are the values of the rotated row words used in `bandRowWord` and `bandColumnWord` (truncated subtraction gives the $\max$).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/BandSupport.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/BandSupport.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Saxl mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicSector

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

def stairBandWord (h s : ℕ) : WordSpace (bandSize h s)
    ((staircase (h+s)).colLen 0 * (staircase (h+s)).colLen 0) :=
  wordTensor _ _ _ (bandRowWord h s ⊗ₜ[ℂ] bandColumnWord h s)

def lowPairLetter (h : ℕ) (x : Fin 4) :
    Fin ((staircase (h+2)).colLen 0 * (staircase (h+2)).colLen 0) :=
  finProdFinEquiv (lowLetter h (Path.parts x).1, lowLetter h (Path.parts x).2)

/- Every Specht shape with at most four rows occurs in the cyclic module
generated by the prescribed two-band vector. -/
end Saxl

namespace Saxl

/- Coordinate subrepresentation using only letters with property A. -/
def alphabetSub (n d : ℕ) (A : Fin d → Prop) : Subrepresentation (wordRep n d) where
  toSubmodule :=
    { carrier := {x | ∀ w, (∃ i, ¬ A (w i)) → x w = 0}
      zero_mem' := by intro w hw; rfl
      add_mem' := by intro x y hx hy w hw; change x w+y w=0; rw [hx w hw,hy w hw,add_zero]
      smul_mem' := by intro c x hx w hw; change c*x w=0; rw [hx w hw,mul_zero] }
  apply_mem_toSubmodule g := by
    intro x hx w hw
    obtain ⟨i,hi⟩ := hw
    apply hx (w ∘ g)
    exact ⟨g⁻¹ i, by simpa using hi⟩

def pairLift {n d D : ℕ} (φ : Fin d → Fin D) :
    Representation.IntertwiningMap (wordRep n (d*d)) (wordRep n (D*D)) :=
  (wordTensorIntertwiner _ _ _).comp (((letterLift φ).tensor (letterLift φ)).comp
    ((wordTensorIntertwiner n d d).ofBijective (wordTensor n d d).bijective).symm.toIntertwiningMap)

def shiftedStairWord (h s : ℕ) := pairLift (highLetter h s) (staircaseWord h)

/- The actual same-high image factors as the smaller Specht tensor cyclic
vector and the exact retained band vector on independent position blocks. -/
/- The width-one band is the genuine trivial constituent required by Pieri. -/
end Saxl

end

end OAI


