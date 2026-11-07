-- Prove2me | Definitions.Def_CompPermOracle_cpO
-- name    : CompPermOracle_cpO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:50:52.687076+00:00
-- url     : https://prove2.me/theorems/79427f23-8bfb-463f-9b9f-61891e6f7021
-- title:
--   The compressed permutation oracle $\mathrm{cpO}$ and its inverse
-- statement:
--   Let $\mathcal L=\mathcal H(\mathcal I)$ be the database register, with basis the partial permutations of $[N]$. Fix $x\in[N]$. For $h$ with $x\notin\mathrm{dom}(h)$ put
--   $$
--   |{+_{x,h}}\rangle=\frac{1}{\sqrt{|Y_h|}}\sum_{y\in Y_h}|h[x\mapsto y]\rangle .
--   $$
--   The spaces $\mathrm{span}(|h\rangle,\{|h[x\mapsto y]\rangle:y\in Y_h\})$ are mutually orthogonal and exhaust $\mathcal L$, and $C_x$ is the unitary that on each of them swaps $|h\rangle$ and $|{+_{x,h}}\rangle$ and fixes the orthogonal complement of their span.
--
--   With $Q_{x,y}=\sum_{f(x)=y}|f\rangle\langle f|$ and $Q_{x,\bot}=\sum_{x\notin\mathrm{dom}(f)}|f\rangle\langle f|$ on $\mathcal L$, set $M_{x,y}=C_xQ_{x,y}C_x^\dagger$ and $M_{x,\bot}=C_xQ_{x,\bot}C_x^\dagger$. The **compressed permutation oracle** at $x$ is
--   $$
--   \mathrm{cpO}_x=I_{\mathcal A}\otimes M_{x,\bot}+\sum_{y}S_y\otimes M_{x,y},
--   $$
--   and $\mathrm{cpO}=\sum_x|x\rangle\langle x|\otimes\mathrm{cpO}_x$. With the flip $F|f\rangle=|f^{-1}\rangle$, the inverse oracle is $\mathrm{cpO}^{-1}_y=(I_{\mathcal A}\otimes F)\mathrm{cpO}_y(I_{\mathcal A}\otimes F)$, and $\mathrm{cpO}^{-1}=\sum_y|y\rangle\langle y|\otimes\mathrm{cpO}^{-1}_y$.
--
--   This is the object whose soundness the mission states.
--
--   **Formalization Note** $C_x$ is given by the closed form $C_x=I-\sum_{h:\,x\notin\mathrm{dom}(h)}|v_h\rangle\langle v_h|$ with $v_h=|h\rangle-|{+_{x,h}}\rangle$. It equals the source's description because the $v_h$ are mutually orthogonal with squared norm $2$, so that each summand is the reflection exchanging $|h\rangle$ and $|{+_{x,h}}\rangle$.
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), p.7; Definitions 3.5, 3.6, p.8

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_swapOp

namespace CompPermOracle

/-- `|+_{x,h}⟩ = |Y_h|^{-1/2} ∑_{y ∈ Y_h} |h[x ↦ y]⟩` (Carolan, Majenz, arXiv:2609.28469 (version
of 2026-11-03, sha256 52ebc507…), p.7). It is used for `x ∉ dom(h)`, where `|Y_h| ≥ 1`. -/
noncomputable def plusState {N : ℕ} (x : Fin N) (h : PartialPerm N) : Hil (PartialPerm N) :=
  ((Real.sqrt ((freeIm h).card : ℝ))⁻¹ : ℂ) • ∑ y ∈ freeIm h, ket (addPair h x y)

/-- The compression unitary `C_x`: on each space `span(|h⟩, {|h[x ↦ y]⟩ : y ∈ Y_h})`, `x ∉ dom(h)`,
it swaps `|h⟩` and `|+_{x,h}⟩` and fixes the orthogonal complement of their span (arXiv:2609.28469,
p.7).

**Formalization Note.** This is the closed form `C_x = I − ∑_h |v_h⟩⟨v_h|`, with
`v_h = |h⟩ − |+_{x,h}⟩`, sum over `h` with `x ∉ dom(h)`. The vectors `v_h` are mutually orthogonal
of squared norm 2, since the listed spaces are mutually orthogonal and `|h⟩ ⊥ |+_{x,h}⟩`. So each
term `I − |v_h⟩⟨v_h|` is the reflection exchanging `|h⟩` and `|+_{x,h}⟩`, fixing the rest. -/
noncomputable def compressU {N : ℕ} (x : Fin N) :
    Hil (PartialPerm N) →L[ℂ] Hil (PartialPerm N) :=
  1 - ∑ h ∈ Finset.univ.filter (fun h : PartialPerm N => NotInDom h x),
    ketBra (ket h - plusState x h) (ket h - plusState x h)

/-- `Q_{x,y} = ∑_{f(x)=y} |f⟩⟨f|` on the database register `ℒ` (arXiv:2609.28469, Definition 3.5,
p.8). -/
noncomputable def assertL {N : ℕ} (x y : Fin N) :
    Hil (PartialPerm N) →L[ℂ] Hil (PartialPerm N) :=
  ∑ f ∈ Finset.univ.filter (fun f : PartialPerm N => f x = some y), ketBra (ket f) (ket f)

/-- `Q_{x,⊥} = ∑_{x ∉ dom(f)} |f⟩⟨f|` on `ℒ` (arXiv:2609.28469, Definition 3.5, p.8). -/
noncomputable def assertLBot {N : ℕ} (x : Fin N) :
    Hil (PartialPerm N) →L[ℂ] Hil (PartialPerm N) :=
  ∑ f ∈ Finset.univ.filter (fun f : PartialPerm N => NotInDom f x), ketBra (ket f) (ket f)

/-- `M_{x,y} = C_x Q_{x,y} C_x†` (arXiv:2609.28469, Definition 3.5, p.8). -/
noncomputable def compM {N : ℕ} (x y : Fin N) :
    Hil (PartialPerm N) →L[ℂ] Hil (PartialPerm N) :=
  (compressU x).comp ((assertL x y).comp (ContinuousLinearMap.adjoint (compressU x)))

/-- `M_{x,⊥} = C_x Q_{x,⊥} C_x†` (arXiv:2609.28469, Definition 3.5, p.8). -/
noncomputable def compMBot {N : ℕ} (x : Fin N) :
    Hil (PartialPerm N) →L[ℂ] Hil (PartialPerm N) :=
  (compressU x).comp ((assertLBot x).comp (ContinuousLinearMap.adjoint (compressU x)))

/-- `cpO_x = I_𝒜 ⊗ M_{x,⊥} + ∑_y S_y ⊗ M_{x,y}` (arXiv:2609.28469, Definition 3.6, eq. (4), p.8). -/
noncomputable def cpOAt {N : ℕ} (x : Fin N) :
    Hil (Ans N × PartialPerm N) →L[ℂ] Hil (Ans N × PartialPerm N) :=
  opTensor (1 : Hil (Ans N) →L[ℂ] Hil (Ans N)) (compMBot x) +
    ∑ y : Fin N, opTensor (swapOp y) (compM x y)

/-- The flip operator `F|f⟩ = |f⁻¹⟩` on `ℒ` (arXiv:2609.28469, Definition 3.6, p.8). -/
noncomputable def flipL {N : ℕ} : Hil (PartialPerm N) →L[ℂ] Hil (PartialPerm N) :=
  ∑ f : PartialPerm N, ketBra (ket f.symm) (ket f)

/-- `cpO⁻¹_y = (I_𝒜 ⊗ F) cpO_y (I_𝒜 ⊗ F)` (arXiv:2609.28469, Definition 3.6, p.8). -/
noncomputable def cpOInvAt {N : ℕ} (y : Fin N) :
    Hil (Ans N × PartialPerm N) →L[ℂ] Hil (Ans N × PartialPerm N) :=
  (opTensor (1 : Hil (Ans N) →L[ℂ] Hil (Ans N)) flipL).comp
    ((cpOAt y).comp (opTensor (1 : Hil (Ans N) →L[ℂ] Hil (Ans N)) flipL))

/-- The full forward compressed oracle `cpO = ∑_x |x⟩⟨x| ⊗ cpO_x` (arXiv:2609.28469, Definition 3.6,
p.8). -/
noncomputable def cpOCtl {N : ℕ} :
    Hil (Fin N × (Ans N × PartialPerm N)) →L[ℂ] Hil (Fin N × (Ans N × PartialPerm N)) :=
  controlled cpOAt

/-- The full inverse compressed oracle `cpO⁻¹ = ∑_y |y⟩⟨y| ⊗ cpO⁻¹_y` (arXiv:2609.28469,
Definition 3.6, p.8). -/
noncomputable def cpOInvCtl {N : ℕ} :
    Hil (Fin N × (Ans N × PartialPerm N)) →L[ℂ] Hil (Fin N × (Ans N × PartialPerm N)) :=
  controlled cpOInvAt

end CompPermOracle


