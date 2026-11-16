-- Prove2me | Definitions.Def_RandPurIso_Completion_Supplement_hiddenDilation
-- name    : RandPurIso_Completion_Supplement_hiddenDilation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:50:36.191525+00:00
-- url     : https://prove2.me/theorems/3252ff6a-5d7b-40e3-b3aa-c55b8b1f8bc7
-- title:
--   The isometries $V^{\mathsf{SAME}},V^{\mathsf{DIFF}}$ and the channels SAME, DIFF
-- statement:
--   Fix $L\ge 1$, $d\ge 2$ and hidden pairs $|\phi_{x,0}\rangle,|\phi_{x,1}\rangle\in\mathbb C^d$ (the first two columns of unitaries $U_x$), and write $P_{x,b}=|\phi_{x,b}\rangle\langle\phi_{x,b}|$. Both channels act on
--
--   $$
--   \mathbf{In}=\mathrm{Span}(|s\rangle)\oplus\mathcal H([L])\otimes\mathcal H([d]),\qquad \dim\mathbf{In}=Ld+1,
--   $$
--
--   with internal registers $\mathbf X=\mathcal H([L])$, $\mathbf B=\mathcal H(\{0,1\})$ and $\mathbf{Extra}$ a copy of $\mathbf{In}$. The isometries $V^{\mathsf{SAME}},V^{\mathsf{DIFF}}:\mathbf{In}\to\mathbf{In}\otimes\mathbf X\otimes\mathbf B\otimes\mathbf{Extra}$ are
--
--   1. $V|s\rangle=\frac1{\sqrt{2L}}\sum_{x\in[L],\,b\in\{0,1\}}|x,\phi_{x,b}\rangle_{\mathbf{In}}|x,b\rangle_{\mathbf{XB}}|s\rangle_{\mathbf{Extra}}$ (both);
--   2. $V^{\mathsf{SAME}}|x,\phi_{x,b}\rangle=|s\rangle|x,b\oplus1\rangle|s\rangle$ and $V^{\mathsf{DIFF}}|x,\phi_{x,b}\rangle=(-1)^b|s\rangle|x,b\oplus1\rangle|s\rangle$;
--   3. $V|x,\psi\rangle=|s\rangle|0\rangle_{\mathbf{XB}}|x,\psi\rangle_{\mathbf{Extra}}$ for $\psi\perp\phi_{x,0},\phi_{x,1}$ (both).
--
--   The channels (Definition 7.6) are
--
--   $$
--   \mathsf{SAME}(\rho)=\mathrm{Tr}_{\mathbf X,\mathbf B,\mathbf{Extra}}\big(V^{\mathsf{SAME}}\rho (V^{\mathsf{SAME}})^\dagger\big),\qquad \mathsf{DIFF}(\rho)=\mathrm{Tr}_{\mathbf X,\mathbf B,\mathbf{Extra}}\big(V^{\mathsf{DIFF}}\rho (V^{\mathsf{DIFF}})^\dagger\big).
--   $$
--
--   These are the hard-to-distinguish channels of §7: one self-switch tells them apart, while forward channel queries need $\Omega(L^{1/3})$ queries.
--
--   **Formalization Note** $|s\rangle$ is `none` in `Option (Fin L × Fin d)`; $|0\rangle_{\mathbf{XB}}$ is $x=0$, $b=0$. The matrix is written as $|\gamma\rangle\langle s|+\sum_{x,b}c_b|s,x,b\oplus1,s\rangle\langle x,\phi_{x,b}|+\sum_x(|s\rangle|0,0\rangle\otimes\iota_{\mathbf{Extra}})(|x\rangle\langle x|\otimes(I-P_{x,0}-P_{x,1}))$; it is the page's isometry whenever the hidden pairs are orthonormal.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, §7, pp. 49–50, Definition 7.6

import Mathlib
import Definitions.Def_RandPurIso_Completion_Supplement_IsDilation
open Matrix

namespace RandPurIso.Completion.Supplement

/-- The channel space `In = Span(|s⟩) ⊕ H([L]) ⊗ H([d])` of dimension `Ld + 1` (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, p. 49):
`none` is the special state `|s⟩`, `some (x, y)` is `|x⟩|y⟩`. -/
abbrev InSp (L d : ℕ) := Option (Fin L × Fin d)

/-- The internal registers `X ⊗ B ⊗ Extra` with `X = H([L])`, `B = H({0,1})` and `Extra` a copy of
`In` (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, p. 49). -/
abbrev HEnv (L d : ℕ) := Fin L × Bool × InSp L d

/-- The hidden state `|φ_{x,b}⟩ ∈ ℂ^d`: column `b` (`b = 0, 1`) of the unitary `U_x` (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, p. 49: "the
first two columns of a Haar-random unitary"). For `d ≥ 2` both columns exist. -/
def pairVec {L d : ℕ} (U : Fin L → Matrix.unitaryGroup (Fin d) ℂ) (x : Fin L) (b : Bool) :
    Fin d → ℂ :=
  fun y => ∑ k : Fin d, if k.val = b.toNat then (U x : Matrix (Fin d) (Fin d) ℂ) y k else 0

/-- **The isometries `V^SAME` (`diff = false`) and `V^DIFF` (`diff = true`)** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, §7, pp. 49–50),
`In → In ⊗ X ⊗ B ⊗ Extra`, built from the hidden pairs `φ_{x,b}` (columns of `U x`):

* `V|s⟩ = (2L)^{-1/2} Σ_{x ∈ [L], b ∈ {0,1}} |x, φ_{x,b}⟩_In |x, b⟩_XB |s⟩_Extra` (both);
* `V^SAME|x, φ_{x,b}⟩ = |s⟩_In |x, b ⊕ 1⟩_XB |s⟩_Extra`,
  `V^DIFF|x, φ_{x,b}⟩ = (−1)^b |s⟩_In |x, b ⊕ 1⟩_XB |s⟩_Extra`;
* `V|x, ψ⟩ = |s⟩_In |0⟩_XB |x, ψ⟩_Extra` for `ψ ⊥ φ_{x,0}, φ_{x,1}` (both).

As a matrix: `V = |γ⟩⟨s| + Σ_{x,b} c_b |s, x, b⊕1, s⟩⟨x, φ_{x,b}| + Σ_x |s⟩|0⟩_XB ⊗ ι_Extra (|x⟩⟨x| ⊗
(I − P_{x,0} − P_{x,1}))`, `c_b = 1` (SAME) or `(−1)^b` (DIFF), `P_{x,b} = |φ_{x,b}⟩⟨φ_{x,b}|`.

**Formalization Note.** Matrix rows are `(In, (x', b', Extra))`; `|0⟩_XB` is `x' = 0` (`x'.val = 0`),
`b' = 0`. The matrix is defined for every family of unitaries; it is the page's isometry when the
hidden pairs are orthonormal (columns of a unitary, `d ≥ 2`, `L ≥ 1`), which every theorem assumes. -/
noncomputable def hiddenDilation {L d : ℕ} (diff : Bool) (U : Fin L → Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix (InSp L d × HEnv L d) (InSp L d) ℂ :=
  fun r j =>
    match j with
    | none =>
        match r.1, r.2.2.2 with
        | some (x, y), none =>
            if r.2.1 = x then ((Real.sqrt (2 * L) : ℝ)⁻¹ : ℂ) * pairVec U x r.2.2.1 y else 0
        | _, _ => 0
    | some (x, y) =>
        (if r.1 = none ∧ r.2.1 = x ∧ r.2.2.2 = none then
            (if diff && !r.2.2.1 then (-1 : ℂ) else 1) * star (pairVec U x (!r.2.2.1) y)
          else 0) +
        (if r.1 = none ∧ r.2.1.val = 0 ∧ r.2.2.1 = false then
            (match r.2.2.2 with
              | some (x', y') =>
                  if x' = x then
                    ((if y' = y then (1 : ℂ) else 0) -
                      ∑ b : Bool, pairVec U x b y' * star (pairVec U x b y))
                  else 0
              | none => 0)
          else 0)

/-- **The channels SAME (`diff = false`) and DIFF (`diff = true`)** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Definition 7.6, p. 50):
`SAME(ρ) = Tr_{X,B,Extra}(V^SAME ρ (V^SAME)†)`, `DIFF(ρ) = Tr_{X,B,Extra}(V^DIFF ρ (V^DIFF)†)`. The
ensembles SAME and DIFF are these channels with the hidden pairs drawn from `hiddenPairMeasure`. -/
noncomputable def hiddenChannel {L d : ℕ} (diff : Bool) (U : Fin L → Matrix.unitaryGroup (Fin d) ℂ)
    (ρ : Matrix (InSp L d) (InSp L d) ℂ) : Matrix (InSp L d) (InSp L d) ℂ :=
  traceEnv (hiddenDilation diff U) ρ

end RandPurIso.Completion.Supplement


