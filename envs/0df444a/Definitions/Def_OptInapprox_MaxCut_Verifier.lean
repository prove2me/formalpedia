-- Prove2me | Definitions.Def_OptInapprox_MaxCut_Verifier
-- name    : OptInapprox_MaxCut_Verifier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:30.374984+00:00
-- url     : https://prove2.me/theorems/c69e3073-cdfa-49ae-a902-4883148e083e
-- title:
--   §8.1, p. 18 — the PCP verifier for MAX-CUT: Long Codes, x∘σ, xμ, acceptance probability, the polling functions g_v
-- statement:
--   The objects of the Long-Code PCP verifier of §8.1, for a Unique Label Cover instance $\mathcal L(V,W,E,[M],\{\sigma_{v,w}\})$ and a parameter $\rho$.
--
--   1. **Neighbourhoods and regularity.** $N(v)=\{w:(v,w)\in E\}$. The instance is *regular on the $V$ side* if $V\neq\emptyset$ and all $|N(v)|$ equal a common $d>0$ (the paper assumes this "using a result from [38]").
--   2. **Long Code (Definition 4).** The code of a label $j\in[M]$ is the dictator $x\mapsto x_j$ on $\{-1,1\}^M$.
--   3. **Notation.** $x\circ\sigma=(x_{\sigma(1)},\dots,x_{\sigma(M)})$, and $x\mu$ is the coordinatewise product.
--   4. **Acceptance probability.** Given supposed Long Codes $f_w:\{-1,1\}^M\to\{-1,1\}$ for $w\in W$: pick $v\in V$ uniformly, two neighbours $w,w'$ of $v$ uniformly and independently, $x\in\{-1,1\}^M$ uniformly, and $\mu\in\{-1,1\}^M$ with independent coordinates equal to $1$ with probability $\tfrac12+\tfrac12\rho$ and $-1$ with probability $\tfrac12-\tfrac12\rho$; accept iff
--   $$f_w(x\circ\sigma_{v,w})\neq f_{w'}\big((x\circ\sigma_{v,w'})\mu\big).$$
--   5. **Polling functions.** $g_v(z)=\mathbf E_{w\sim v}\big[f_w(z\circ\sigma_{v,w})\big]$, the average over the neighbours of $v$.
--
--   These objects state the completeness (§8.2) and soundness (§8.3) of the reduction from Unique Label Cover to MAX-CUT.
--
--   **Formalization Note.** A proof is `F : W → ({-1,1}^M → Bool)`, with $f_w=$ `pm ∘ F w`. With TRUE $=-1$ the coordinatewise product is `xor`. The acceptance probability is a finite weighted average; a vertex with no neighbours contributes $0$, and $V=\emptyset$ gives $0$; regularity excludes both.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 6 (Definition 4), p. 18, §8.1 The PCP

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_Cube
import Definitions.Def_OptInapprox_MaxCut_UGC

namespace OptInapprox.MaxCut

noncomputable section

namespace ULC

/-- The neighbours `w ∈ W` of a left vertex `v`. -/
def nbrs (L : ULC) (v : Fin L.nV) : Finset (Fin L.nW) :=
  Finset.univ.filter fun w => (v, w) ∈ L.E

/-- Regularity on the `V` side (§8.1, "using a result from [38]"): `V` is nonempty and every
`v ∈ V` has the same positive number of neighbours. -/
def IsVRegular (L : ULC) : Prop :=
  0 < L.nV ∧ ∃ d : ℕ, 0 < d ∧ ∀ v, (L.nbrs v).card = d

end ULC

/-- The Long Code of the label `j ∈ [M]` (Definition 4): the dictator `x ↦ x_j`. -/
def longCode {M : ℕ} (j : Fin M) : (Fin M → Bool) → Bool := fun x => x j

/-- `x ∘ σ = (x_{σ(1)}, …, x_{σ(M)})` (§8.1). -/
def compose {M : ℕ} (x : Fin M → Bool) (σ : Equiv.Perm (Fin M)) : Fin M → Bool :=
  fun i => x (σ i)

/-- The coordinatewise product `xμ` of two strings in `{-1,1}^M` (§8.1); with TRUE ↦ `-1` it is
`xor` on bits, since `pm (xor a b) = pm a * pm b`. -/
def coordMul {M : ℕ} (x μ : Fin M → Bool) : Fin M → Bool := fun i => xor (x i) (μ i)

/-- The probability of the noise string `μ` in the verifier (§8.1): each coordinate is
independently `1` with probability `1/2 + ρ/2` and `-1` with probability `1/2 - ρ/2`. -/
def muWeight {M : ℕ} (ρ : ℝ) (μ : Fin M → Bool) : ℝ := ∏ i, (1 + ρ * pm (μ i)) / 2

/-- The acceptance probability of the PCP verifier for MAX-CUT with parameter `ρ` (§8.1) on the
proof `F` (the supposed Long Codes `f_w = F w`, boolean-valued): pick `v ∈ V` uniformly, two
neighbours `w, w'` of `v` uniformly and independently, `x` uniform and `μ` as in `muWeight`; accept
iff `f_w(x ∘ σ_{v,w}) ≠ f_{w'}((x ∘ σ_{v,w'}) μ)`. -/
def accProb (L : ULC) (ρ : ℝ) (F : Fin L.nW → (Fin L.M → Bool) → Bool) : ℝ :=
  (L.nV : ℝ)⁻¹ * ∑ v, ((L.nbrs v).card : ℝ)⁻¹ ^ 2 *
    ∑ w ∈ L.nbrs v, ∑ w' ∈ L.nbrs v, (2 ^ L.M : ℝ)⁻¹ * ∑ x, ∑ μ, muWeight ρ μ *
      (if F w (compose x (L.σ v w)) ≠ F w' (coordMul (compose x (L.σ v w')) μ) then 1 else 0)

/-- The "polling" function of (6): `g_v(z) = E_{w ∼ v}[f_w(z ∘ σ_{v,w})]`, the average over the
neighbours `w` of `v` (with `f_w = pm ∘ F w`). -/
def gv (L : ULC) (F : Fin L.nW → (Fin L.M → Bool) → Bool) (v : Fin L.nV) (z : Fin L.M → Bool) :
    ℝ :=
  ((L.nbrs v).card : ℝ)⁻¹ * ∑ w ∈ L.nbrs v, pm (F w (compose z (L.σ v w)))

end

end OptInapprox.MaxCut


