-- Prove2me | Definitions.Def_CopylessCRA_returnWords
-- name    : CopylessCRA_returnWords
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:47:08.638192+00:00
-- url     : https://prove2.me/theorems/2867c0a0-a987-428f-8941-2fa394040546
-- title:
--   Finite control of §4: $\delta(S,w)$, $S_{ret}$, $e=t^{m_0}$, return words $L_{S_{ret}}$, $\mathcal K$, and the local spaces $W$, $N$, $K_u$ of Lemma 15
-- statement:
--   Let $\delta:S\times\Sigma\to S$ be a complete deterministic control on a finite set $S$.
--
--   1. $\delta(S,w)=\{\delta(s,w):s\in S\}$; $t$ is a word for which $|\delta(S,t)|$ is minimal, $S_{ret}=\delta(S,t)$, $m_0=|S_{ret}|!$ and $e=t^{m_0}$.
--   2. The return words $L_{S_{ret}}=\{z\in\Sigma^*:\delta(r,z)=r\ \forall r\in S_{ret}\}$.
--   3. $\mathcal K$ is the Zariski closure in $GL_d(\overline{\mathbb Q})$ of $\{M_z:z\in L_{S_{ret}}\}$.
--   4. For a CCRA and a state $q$: $o_s=\omega_{\delta(q,s)}\circ P_{q,s}$, $W=\operatorname{span}\{o_s\}$, and for a valuation $x_u$, $N=\{h\in W:(B_zh)(x_u)=0\ \forall z\in L_{S_{ret}}\}$ with $B_z=B_{P_{q,z}}$.
--   5. For a representation, $K_u=\{v\in\mathbb Q^d:\lambda M_{ue}M_zv=0\ \forall z\in L_{S_{ret}}\}$.
--
--   These are the objects of Lemmas 13–15.
-- source:
--   Zeng–Cao–Dai–Wang–Ding, Copyless Cost Register Automata and Algebraic Groups, STOC 2027 submission (manuscript sha256 434d3094df2665371c402d5b5291b3c7f3a27a0d79384e4a8ec3ca3a46a92543), §4, p.10 (PDF p.12), including Lemma 15

import Mathlib
import Definitions.Def_CopylessCRA_CCRA
import Definitions.Def_CopylessCRA_IsRep
import Definitions.Def_CopylessCRA_zariskiClosure
import Definitions.Def_CopylessCRA_IsCopylessMap
open Matrix

namespace CopylessCRA

section Control

variable {S α : Type*} [Fintype S] [DecidableEq S]

/-- The image `δ(S, w) = {δ(s, w) : s ∈ S}` of the control states under a word. Zeng–Cao–Dai–Wang–
Ding, *Copyless Cost Register Automata and Algebraic Groups*, STOC 2027 submission (manuscript
sha256 434d3094…), §4, p.10 (PDF p.12). -/
def imageWord (δ : S → α → S) (w : List α) : Finset S :=
  Finset.univ.image fun s => deltaWord δ s w

/-- `t` is a word for which the image `δ(S, t)` has minimum size (§4, p.10). Then
`S_ret = imageWord δ t`. -/
def IsMinImageWord (δ : S → α → S) (t : List α) : Prop :=
  ∀ w : List α, (imageWord δ t).card ≤ (imageWord δ w).card

/-- `e = t^{m₀}` with `m₀ = |S_ret|!` and `S_ret = δ(S, t)` (§4, p.10). -/
def eWord (δ : S → α → S) (t : List α) : List α :=
  (List.replicate (imageWord δ t).card.factorial t).flatten

/-- The **return words** `L_{S_ret} = {z ∈ Σ* : δ(r, z) = r for all r ∈ S_ret}` (§4, p.10). -/
def returnWords (δ : S → α → S) (Sret : Finset S) : Set (List α) :=
  {z | ∀ s ∈ Sret, deltaWord δ s z = s}

end Control

/-- `𝒦`, the Zariski closure in `GL_d(ℚ̄)` of the word matrices `{M_z : z ∈ L}` (§4, p.10, with
`L = L_{S_ret}`). -/
def returnClosure {α : Type*} {d : ℕ} (M : α → Matrix (Fin d) (Fin d) ℚ) (L : Set (List α)) :
    Set (Matrix (Fin d) (Fin d) Qbar)ˣ :=
  zariskiClosure {g | ∃ z ∈ L, (g : Matrix (Fin d) (Fin d) Qbar) = castMat (wordMat M z)}

namespace CCRA

variable {α : Type*} (C : CCRA α)

/-- `o_s = ω_{δ(q,s)} ∘ P_{q,s} ∈ V_r` (Lemma 15, p.10, PDF p.12). -/
noncomputable def outPoly (q : C.S) (s : List α) : MvPolynomial (Fin C.r) ℚ :=
  pullback (C.runPoly q s) (C.out (deltaWord C.δ q s)).toPoly

/-- `W = span{o_s : s ∈ Σ*}` of Lemma 15 (p.10). -/
noncomputable def localW (q : C.S) : Submodule ℚ (MvPolynomial (Fin C.r) ℚ) :=
  Submodule.span ℚ (Set.range (C.outPoly q))

/-- `N = {h ∈ W : (B_z h)(x_u) = 0 for all z ∈ L}` of Lemma 15 (p.10), with `B_z = B_{P_{q,z}}`. -/
noncomputable def localN (q : C.S) (L : Set (List α)) (xu : Fin C.r → ℚ) :
    Submodule ℚ (MvPolynomial (Fin C.r) ℚ) where
  carrier := {h | h ∈ C.localW q ∧ ∀ z ∈ L, MvPolynomial.eval xu (pullback (C.runPoly q z) h) = 0}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨add_mem ha hb, fun z hz => by simp [ha' z hz, hb' z hz]⟩
  zero_mem' := ⟨zero_mem _, fun z _ => by simp⟩
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    exact ⟨Submodule.smul_mem _ c ha, fun z hz => by simp [ha' z hz]⟩

end CCRA

/-- `K_u = {v ∈ ℚ^d : λ M_{v₀} M_z v = 0 for all z ∈ L}` of Lemma 15 (p.10), with `v₀ = ue`. -/
def localK {α : Type*} {d : ℕ} (lam : Fin d → ℚ) (M : α → Matrix (Fin d) (Fin d) ℚ)
    (v0 : List α) (L : Set (List α)) : Submodule ℚ (Fin d → ℚ) where
  carrier := {v | ∀ z ∈ L, lam ⬝ᵥ ((wordMat M v0 * wordMat M z) *ᵥ v) = 0}
  add_mem' := by
    intro a b ha hb z hz
    simp [Matrix.mulVec_add, dotProduct_add, ha z hz, hb z hz]
  zero_mem' := by intro z _; simp
  smul_mem' := by
    intro c a ha z hz
    simp [Matrix.mulVec_smul, dotProduct_smul, ha z hz]

end CopylessCRA


