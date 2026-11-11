-- Prove2me | Definitions.Def_SmallBiasPRF_Ftilde
-- name    : SmallBiasPRF_Ftilde
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:11:07.730198+00:00
-- url     : https://prove2.me/theorems/f84dd4a7-3743-4ddc-bc89-233121e9caa1
-- title:
--   The short-key expander-walk construction $\tilde F_{k_e,w,z}$ and its single-bit variant
-- statement:
--   Let $NB$ describe a $d$-regular multigraph on $\Omega=[m_1]$. The expander walk key space is $K_{\exp}=\Omega\times[d]^{m_2-1}$, and a key $k_e$ defines the selector $\tilde\pi_{k_e}(j)=x_j$, the $j$-th vertex of its walk. The **short-key construction** takes the key $(k_e,w,z)\in K_{\exp}\times\{0,1,2\}^{m_2}\times\{0,1,2\}^{m_2}$ and an input $a\in\{0,1\}^n$:
--
--   $$\tilde F_{k_e,w,z}(a)=F_{\tilde\pi_{k_e},w,z}(a)=R\big(G_{w,z}(\mathrm{map}_{\tilde\pi_{k_e}}(H(a)))\big),$$
--
--   and for $S\subseteq[m_2]$ its single-bit variant is $\tilde F^S_{k_e,w,z}(a)=F^S_{\tilde\pi_{k_e},w,z}(a)$. The full key is chosen uniformly from $K_{\exp}\times\{0,1,2\}^{m_2}\times\{0,1,2\}^{m_2}$, so the key length is $O(n)$ when $d$ is constant and $m_1,m_2=O(n)$.
--
--   **Formalization Note** The key is a triple $((x_1,e),w,z)$ with $e:$ `Fin (m₂ - 1) → Fin d`; the selector is the walk with 0-based indices.
-- source:
--   Dinur–Ishai, Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with Exponentially Small Bias, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), §4.3, pp.15–16 (PDF 18–19)

import Mathlib
import Definitions.Def_SmallBiasPRF_basicF
import Definitions.Def_SmallBiasPRF_IsSpectralExpander

namespace SmallBiasPRF

/-- The expander walk key space `K_exp = Ω × [d]^{m₂−1}` with `Ω = [m₁]` (§4.3, p.15 (PDF p.18)). -/
abbrev KeyExp (m₁ m₂ d : ℕ) : Type := Fin m₁ × (Fin (m₂ - 1) → Fin d)

/-- The full key space `K_exp × {0,1,2}^{m₂} × {0,1,2}^{m₂}` of the short-key construction
(§4.3, p.16 (PDF p.19)). -/
abbrev FullKey (m₁ m₂ d : ℕ) : Type := KeyExp m₁ m₂ d × (Fin m₂ → ZMod 3) × (Fin m₂ → ZMod 3)

/-- The bit selector sequence `π̃_{k_e} : [m₂] → [m₁]`, `π̃_{k_e}(j) = x_j`, the expander walk of
the key `k_e` (§4.3, p.16 (PDF p.19)). -/
def selTilde {m₁ m₂ d : ℕ} (NB : Fin m₁ → Fin d → Fin m₁) (ke : KeyExp m₁ m₂ d) : Fin m₂ → Fin m₁ :=
  walk NB ke.1 ke.2

/-- The **short-key construction** `F̃_{k_e,w,z}(a) = F_{π̃_{k_e},w,z}(a) = R(G_{w,z}(map_{π̃_{k_e}}(H(a))))`
(§4.3, p.16 (PDF p.19)).
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), §4.3, p.16 (PDF p.19).

**Formalization Note.** The key is `κ = ((x₁, e), w, z) : FullKey m₁ m₂ d`; the selector is the
expander walk `walk NB x₁ e` (0-based). In the theorems the key is uniform on `FullKey m₁ m₂ d`. -/
def Ftilde {n m₁ m₂ d : ℕ} (H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2))
    (R : (Fin m₂ → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (NB : Fin m₁ → Fin d → Fin m₁)
    (κ : FullKey m₁ m₂ d) (a : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  basicF H R (selTilde NB κ.1) κ.2.1 κ.2.2 a

/-- The single-bit variant `F̃^S_{k_e,w,z}(a) = F^S_{π̃_{k_e},w,z}(a) = G^S_{w,z}(map_{π̃_{k_e}}(H(a)))`
for `S ⊆ [m₂]` (§4.3.2, p.16 (PDF p.19)). It does not involve `R`.
Dinur–Ishai, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), §4.3.2, p.16. -/
def FtildeS {n m₁ m₂ d : ℕ} (H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2))
    (NB : Fin m₁ → Fin d → Fin m₁) (S : Finset (Fin m₂)) (ke : KeyExp m₁ m₂ d)
    (w z : Fin m₂ → ZMod 3) (a : Fin n → ZMod 2) : ZMod 2 :=
  basicFS H S (selTilde NB ke) w z a

end SmallBiasPRF


