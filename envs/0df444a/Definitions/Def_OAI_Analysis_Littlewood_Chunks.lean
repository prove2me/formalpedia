-- Prove2me | Definitions.Def_OAI_Analysis_Littlewood_Chunks
-- name    : OAI_Analysis_Littlewood_Chunks
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:11:44.119568+00:00
-- url     : https://prove2.me/theorems/ed366186-1a0e-4302-9a95-846901fdea1f
-- title:
--   Periodic slot layouts modulo a prime: slot centers, signed sites, chunk choices, and the interior catalogue
-- statement:
--   Fix $r$ slots. For lengths $L=(L_0,\dots,L_{r-1})\in\mathbb{N}^r$ let $\mathrm{pre}_L(i)=\sum_{j<i}L_j$ be the prefix sums and $P_L=\sum_{j<r}L_j$ the period length. Positions are natural numbers, later read in $\mathbb{Z}/q\mathbb{Z}$; differences $R-1$, $R-2$ of natural numbers are truncated at $0$.
--
--   1. **Left end of a slot.** For a repetition number $R$, a shift $s$, a chunk index $k$, a period index $p$ and a slot $i$,
--   $$
--   \mathrm{left}(s,k,p,i)=k\,R\,P_L+p\,P_L+s+\mathrm{pre}_L(i).
--   $$
--   The sites of slot $i$ are $\mathrm{left}+1,\dots,\mathrm{left}+L_i$: chunk $k$ is the block of $RP_L$ positions starting at $kRP_L$, inside which the pattern of $r$ consecutive slots of lengths $L_0,\dots,L_{r-1}$ is repeated with period $P_L$ and shifted by $s$.
--
--   2. **Signed site.** For $q\in\mathbb{N}$, a sign $e\in\{\mathrm{true},\mathrm{false}\}$ and $x\in\mathbb{N}$, $\mathrm{sgn}_q(e,x)\in\mathbb{Z}/q\mathbb{Z}$ is the class of $x$ if $e$ is true and of $-x$ otherwise.
--
--   3. **Odd lengths and slot centers.** For $d\in\mathbb{N}^r$ take the odd lengths $L_i=2d_i+1$ and write $P=P_L$. The center of slot $i$ is $\mathrm{center}(s,k,p,i)=\mathrm{left}(s,k,p,i)+d_i+1$, its middle site.
--
--   4. **Interior sites.** $\mathrm{int}(k,t)=k\,R\,P+P+1+t$.
--
--   5. **Slot choices.** A slot choice for $K$ chunks is a map $\omega$ assigning to each chunk $k<K$ a pair $\omega(k)=(s_k,e_k)$ of a shift $s_k\in\{0,\dots,P-1\}$ and a sign $e_k$.
--
--   6. **Hit residues.** A residue $u\in\mathbb{Z}/q\mathbb{Z}$ is hit in slot $i$ under $\omega$ if
--   $$
--   u=\mathrm{sgn}_q\bigl(e_k,\ \mathrm{center}(s_k,k,p,i)\bigr)\quad\text{for some chunk }k<K\text{ and some period }p<R-1.
--   $$
--
--   7. **Short residues.** $\mathrm{Short}_q(B)=\{c \bmod q:\ c\in\mathbb{Z},\ -B\le c\le B\}$.
--
--   8. **Interior catalogue.** Its index set is $\{0,\dots,K-1\}\times\{0,\dots,(R-2)P-1\}\times\{\mathrm{true},\mathrm{false}\}$, the value of $(k,t,e)$ is $\mathrm{sgn}_q(e,\mathrm{int}(k,t))$, and the catalogue set is the set of all these values in $\mathbb{Z}/q\mathbb{Z}$.
--
--   These objects build, inside $\mathbb{Z}/q\mathbb{Z}$, the random target sets used to pack signed arcs on the circle. The positions are cut into $K$ chunks of length $RP$; in each chunk the pattern of slots of odd lengths $2d_i+1$ is translated by a shift and multiplied by a sign, chosen independently for each chunk. When $2KRP<q$, every slot has exactly $K(R-1)$ hit residues, the catalogue set has exactly $2K(R-2)P$ elements, each catalogue residue is hit in slot $i$ exactly when the choice $\omega(k)$ of its own chunk takes one specific value, and two catalogue residues from the same chunk have sum or difference in $\mathrm{Short}_q(RP)$. This independence across chunks makes the slot densities concentrate, while the separation of slot centers turns a matching of hit residues into a packing of disjoint arcs.
--
--   **Formalization Note** The definitions are `slotPrefix`, `periodLength`, `slotLeft L R shift chunk period i`, `signedSite q e x`, the abbreviation `oddLengths d`, `siteCenter d R shift chunk period i`, `interiorSite d R k t`, the type `SlotChoices d K` of maps `Fin K → Fin P × Bool`, the `Prop` `slotHit d R K q i ω u` with period index in `Fin (R-1)`, `shortResidues q B` (the image of `Finset.Icc (-B) B` in `ZMod q`), the type `InteriorCatalog d R K`, `catalogValue` and `catalogSet`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Chunks.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Chunks.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the AsymptoticallyMinimalLittlewood mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank

namespace OAI

universe uJ

namespace AsymptoticallyMinimalLittlewood
namespace Packing
noncomputable section
open scoped BigOperators
open Finset

variable {r : ℕ}
def slotPrefix (L : Fin r → ℕ) (i : Fin r) : ℕ := ∑ j ∈ Finset.Iio i, L j

def periodLength (L : Fin r → ℕ) : ℕ := ∑ j, L j

/-- Site immediately to the left of a slot. The actual sites are
left+1,...,left+L_i. Each full chunk keeps R-1 translated periods. -/
def slotLeft (L : Fin r → ℕ) (R : ℕ) (shift chunk period : ℕ) (i : Fin r) : ℕ :=
  chunk*(R*periodLength L)+period*periodLength L+shift+slotPrefix L i

def signedSite (q : ℕ) (e : Bool) (x : ℕ) : ZMod q := if e then x else -x

abbrev oddLengths (d : Fin r → ℕ) : Fin r → ℕ := fun i ↦ 2*d i+1

def siteCenter (d : Fin r → ℕ) (R shift chunk period : ℕ) (i : Fin r) : ℕ :=
  slotLeft (oddLengths d) R shift chunk period i+d i+1

def interiorSite (d : Fin r → ℕ) (R k t : ℕ) : ℕ :=
  k*(R*periodLength (oddLengths d))+periodLength (oddLengths d)+1+t

abbrev SlotChoices (d : Fin r → ℕ) (K : ℕ) :=
  Fin K → Fin (periodLength (oddLengths d)) × Bool

def slotHit (d : Fin r → ℕ) (R K q : ℕ) (i : Fin r)
    (ω : SlotChoices d K) (u : ZMod q) : Prop :=
  ∃ k : Fin K, ∃ p : Fin (R-1),
    u=signedSite q (ω k).2 (siteCenter d R (ω k).1 k p i)

/-- The finite residue neighborhood used to detect same-chunk collisions. -/
def shortResidues (q B : ℕ) : Finset (ZMod q) :=
  (Finset.Icc (-(B : ℤ)) B).image (fun c : ℤ ↦ (c : ZMod q))

end
end Packing
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset
variable {r : ℕ}

abbrev InteriorCatalog (d : Fin r → ℕ) (R K : ℕ) :=
  Fin K × Fin ((R-2)*periodLength (oddLengths d)) × Bool

def catalogValue (d : Fin r → ℕ) (R K q : ℕ) (c : InteriorCatalog d R K) : ZMod q :=
  signedSite q c.2.2 (interiorSite d R c.1 c.2.1)

def catalogSet (d : Fin r → ℕ) (R K q : ℕ) : Finset (ZMod q) :=
  Finset.univ.image (catalogValue d R K q)

attribute [local instance] Classical.propDecidable

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI


