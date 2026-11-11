-- Prove2me | Definitions.Def_ShamirLLR_classG
-- name    : ShamirLLR_classG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:27:22.208826+00:00
-- url     : https://prove2.me/theorems/539d37cb-9ff1-4575-87a9-932b851a41e4
-- title:
--   Definition 4.1: the smooth class $G_{p,3}$
-- statement:
--   Fix a nonempty finite collection $\mathcal N$ of degree-two filtered nilmanifolds with adapted Mal'cev bases, an integer $D\ge1$ bounding their dimensions, $Q\ge1$ and $R=2D+4$. For an odd prime $p$, the class $G_{p,3}$ consists of the probability maps $f_{\mathrm{nil}}:\mathbb F_p\to[0,1]$ of the form
--   $$
--   f_{\mathrm{nil}}(\bar z)=F\bigl(g_0g_1^zg_2^{\binom z2}\Gamma\bigr),
--   $$
--   where $(G/\Gamma,G_\bullet,X)\in\mathcal N$, $g_0,g_1\in G$, $g_2\in G_2$, $g_1^p\in\Gamma$, $g_2^p\in\Gamma_2$, and $F\in C^R(G/\Gamma;[0,1])$ with $\|F\|_{C^R(X)}\le Q$. The power conditions make the value independent of the integer representative $z$ of $\bar z$.
--
--   This is the structured class approximating every one-bit leakage function in $U^3$.
--
--   **Formalization Note** $\mathcal N$ is a set of `LSS.Nilmanifold 2`; its finiteness, nonemptiness and the dimension bound are hypotheses of the statements that use the class. $\Gamma_2=\Gamma\cap G_2$.
-- source:
--   Hwang–Maji–Shkredov–Ye, Local Leakage Resilience of Multiplication-friendly Shamir Secret Sharing (manuscript, 2 Nov 2026; held version, sha256 fcd6871f…), Definition 4.1, p.26, with §4.1, pp.24–26 (PDF pp.25–27)

import Mathlib
import Definitions.Def_LSSNil
import Definitions.Def_ShamirLLR_nilCoords
import Definitions.Def_ShamirLLR_nilSmooth

set_option autoImplicit false

namespace ShamirLLR

/-- **Definition 4.1 (Class `G_{p,3}`).** For an odd prime `p`, a nonempty finite collection `N`
of degree-two filtered nilmanifolds with adapted Mal'cev bases, an integer `D ≥ 1` bounding their
dimensions, `Q ≥ 1` and `R = 2D + 4`, `G_{p,3}` consists of the probability maps
`f_nil : 𝔽_p → [0, 1]` of the form `f_nil(z̄) = F(g₀ g₁^z g₂^{(z choose 2)} Γ)` with
`(G/Γ, G_•, X) ∈ N`, `g₀, g₁ ∈ G`, `g₂ ∈ G₂`, `g₁^p ∈ Γ`, `g₂^p ∈ Γ₂`, `F ∈ C^R(G/Γ; [0, 1])` and
`‖F‖_{C^R(X)} ≤ Q`.

Source: Hwang–Maji–Shkredov–Ye, manuscript of 2 Nov 2026 (held version, sha256 fcd6871f…),
Definition 4.1, p.26, with the data of §4.1, pp.24–26 (`K = D + 2`, `R = 2D + 4`).

**Formalization Note.** `N` is a set of `LSS.Nilmanifold 2` (finiteness, nonemptiness and the
dimension bound are hypotheses of the statements that use the class). `Γ₂ = Γ ∩ G₂`. The map is
given at every integer representative `z` of `z̄` (the power conditions make this independent of
the representative). The readout `F : G → ℝ` is right-`Γ`-invariant, `C^R`, `[0,1]`-valued on
`G`. -/
def classG (p : ℕ) (N : Set (LSS.Nilmanifold 2)) (D : ℕ) (Q : ℝ) : Set (ZMod p → ℝ) :=
  {f | ∃ G ∈ N, ∃ g₀ g₁ g₂ : G.Mat, G.Mem g₀ ∧ G.Mem g₁ ∧ G.MemFil 2 g₂ ∧
      G.MemΓ (g₁ ^ p) ∧ G.MemΓ (g₂ ^ p) ∧ G.MemFil 2 (g₂ ^ p) ∧
      ∃ F : G.Mat → ℝ, IsCR G (2 * D + 4) F ∧ (∀ x : G.Mat, G.Mem x → 0 ≤ F x ∧ F x ≤ 1) ∧
        CRNormLE G (2 * D + 4) Q F ∧ ∀ z : ℤ, f (z : ZMod p) = F (quadOrbit G g₀ g₁ g₂ z)}

end ShamirLLR


