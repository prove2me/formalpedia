-- Prove2me | Definitions.Def_QuadStatRE_Main_Iterated
-- name    : QuadStatRE_Main_Iterated
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:47:00.993253+00:00
-- url     : https://prove2.me/theorems/d2489d50-84b9-4de6-b12e-acc748e318d3
-- title:
--   The iterated encoder $\mathrm{Enc}_{r,t}$, its natural simulator $\mathrm{Sim}_{r,t}$ and the iterated leakage $W_r$
-- statement:
--   The **depth-$r$ encoder** $\mathrm{Enc}_{r,t}$ (§5.1, p. 24) is the complete 15-ary recursion obtained by applying the RM sharing step $r$ times and the basic gadget $\mathrm{Enc}_t$ (Construction 1) at every leaf: $\mathrm{Enc}_{0,t}=\mathrm{Enc}_t$ and $\mathrm{Enc}_{r+1,t}$ is the amplification (Construction 3) of $\mathrm{Enc}_{r,t}$. Only leaf transcripts are output.
--
--   The **natural simulator** $\mathrm{Sim}_{r,t}(b)$ (§5.2, p. 25), given the permitted output $b$, chooses $(x,y,z)$ uniformly, sets $w=b+xyz$, and runs $\mathrm{Enc}_{r,t}$ on $(x,y,z,w)$ with a fresh uniform tape.
--
--   The **iterated leakage** (p. 25) is
--   $$W_{0,s}=\text{the equality leakage},\qquad W_{r+1,s}=\mathcal A_s(W_r),$$
--   on the alphabet $\Omega_0=G\times\mathbb F_2$, $\Omega_{r+1}=\Omega_r^I$; $\tau_r=\tau(W_r)$.
--
--   These are the objects of the privacy amplification theorem: $\mathrm{Enc}_{r,t}$ is a leaky encoding with leakage $W_{r,s}$, and its privacy error is controlled by $\tau_r$.
--
--   **Formalization Note.** The simulator's coins are the uniform triple and a uniform encoder tape. $I$ is indexed as in the RM sharing definition.
-- source:
--   Applebaum, Quadratic Statistical Randomized Encoding for All Functions, STOC 2027 submission (manuscript sha256 000cbf4e…), pp. 24–25, §5.1–5.2

import Mathlib
import Definitions.Def_QuadStatRE_Main_LeakageFamily
import Definitions.Def_QuadStatRE_Main_RMSharing

namespace QuadStatRE.Main

open QuadraticRE

/-- The leakage transcript alphabet at depth `r` (Applebaum, *Quadratic Statistical Randomized
Encoding for All Functions*, STOC 2027 submission, §5.2, p. 25): `G × F₂` (the equality leakage
`(V, e)`) at depth `0`, and fifteen depth-`r` transcripts at depth `r + 1`. -/
def Omega : ℕ → Type
  | 0 => G × F2
  | r + 1 => Fin 15 → Omega r

/-- Each alphabet is finite. -/
instance instFintypeOmega : (r : ℕ) → Fintype (Omega r)
  | 0 => inferInstanceAs (Fintype (G × F2))
  | r + 1 => letI := instFintypeOmega r; inferInstanceAs (Fintype (Fin 15 → Omega r))

/-- The iterated leakage (§5.2, p. 25): `W_{0,s}` the equality leakage, `W_{r+1,s} = A_s(W_r)`. -/
noncomputable def Wr : (r : ℕ) → G → Omega r → ℝ
  | 0 => W0
  | r + 1 => amp (Wr r)

/-- The depth-`r` encoder `Enc_{r,t}` (§5.1, p. 24): "the complete 15-ary recursion obtained by
applying the sharing step `r` times and the basic gadget (construction 1) at every leaf". -/
def encR : ℕ → ℕ → Enc4
  | 0, t => basicEnc t
  | r + 1, t => amplify (encR r t)

/-- The natural simulator `Sim_{r,t}(b)` (§5.2, p. 25): "given the permitted output `b`, choose
`(x, y, z)` uniformly, set `w = b + xyz`, and run the same encoder". Its coins are the uniform triple
`s` and a uniform encoder tape. -/
def simR (r t : ℕ) (b : F2) (c : G × (Fin (encR r t).ρ → F2)) : Fin (encR r t).m → F2 :=
  (encR r t).desc.eval (mkInput c.1 (b + c.1 0 * c.1 1 * c.1 2)) c.2

end QuadStatRE.Main


