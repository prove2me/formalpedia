-- Prove2me | Definitions.Def_StallEconomy_Magnet_Setting
-- name    : StallEconomy_Magnet_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T22:56:27.672727+00:00
-- url     : https://prove2.me/theorems/f252419b-0830-427d-a599-1aef213ce99d
-- title:
--   §3.3, pp. 13–17 — service grid, magnet rule, and rendezvous transition matrix
-- statement:
--   In the service zone's edge coordinates, let the customer grid be $G_k=\{0,\ldots,k\}^2$. Let $h=\phi k$ be the integer number of grid units a customer may walk, where $\phi=r/(\sqrt2R)$ and $2h\le k$. The possible stall locations form the **inner diamond** $\mathcal I_0=[h,k-h]^2\cap\mathbb Z^2$. Type-1 origins are in $\mathcal I_1=[2h,k-2h]^2\cap\mathbb Z^2$; all other origins in $\mathcal I_0$ are type 2. The closed **small diamond** around $z_o=(x_o,y_o)$ is $\mathcal I(z_o)=[x_o-h,x_o+h]\times[y_o-h,y_o+h]\cap\mathbb Z^2$.
--
--   Outside $\mathcal I(z_o)$, the customer's position lies in exactly one of the paper's eight regions $\mathcal S_1,\ldots,\mathcal S_8$, whose boundary inequalities are those of §3.3. Each region selects one of the eight prescribed arrowheads $a^i(z_c)[2]$. If the customer is inside $\mathcal I(z_o)$, the stall stays at $z_o$. At a type-1 origin it otherwise follows the selected arrow. At a type-2 origin it follows the arrow when its head is in $\mathcal I_0$, and otherwise rotates the arrow as in Definition 2(I)b or (I)c to keep the rendezvous in $\mathcal I_0$. This defines $m_{k,h}(z_o,z_c)$.
--
--   The set $\mathcal A(z_o,z_d)$ consists of all customer grid points $z_c$ for which $m_{k,h}(z_o,z_c)=z_d$. Uniform customer demand on the full grid gives the **transition matrix**
--   $$
--   \mathbb P(z_o,z_d)=\frac{|\mathcal A(z_o,z_d)|}{(k+1)^2},\qquad z_o,z_d\in\mathcal I_0.
--   $$
--
--   This module supplies the paper-specific model used by every theorem in this mission.
--
--   **Formalization Note** The paper calls $\mathcal A$ a set of customer-movement arrows, yet its row count and Case I(IX) count customers in $\mathcal I(z_o)$ who do not move. The definition counts customer locations, including those self-loop cases; each customer corresponds to one transition event. Lean's region indices $0,\ldots,7$ correspond to the paper's $1,\ldots,8$. Coordinates and interval endpoints are integers, so no natural-number subtraction truncates $k-h$.
-- source:
--   Cao, Qi, Stall Economy: The Value of Mobility in Retail on Wheels, SSRN 3711896 (manuscript), pp. 13–17, Definitions 1–2 and transition probability

import Mathlib
import Definitions.Def_MarkovChain

namespace StallEconomy.Magnet

/-- Grid points of the full service zone, in coordinates along its two lower edges. -/
noncomputable def grid (k : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc 0 (k : ℤ) ×ˢ Finset.Icc 0 (k : ℤ)

/-- The inner diamond 𝓘₀ in the paper's edge coordinates, with `h = ϕk`. -/
noncomputable def inner (k h : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (h : ℤ) ((k : ℤ) - h) ×ˢ
    Finset.Icc (h : ℤ) ((k : ℤ) - h)

/-- The set 𝓘₁ of type-1 stall origins. -/
noncomputable def type1 (k h : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc ((2 * h : ℕ) : ℤ) ((k : ℤ) - 2 * (h : ℤ)) ×ˢ
    Finset.Icc ((2 * h : ℕ) : ℤ) ((k : ℤ) - 2 * (h : ℤ))

/-- The small diamond 𝓘(zₒ), a closed square in edge coordinates. -/
noncomputable def smallDiamond (h : ℕ) (zo : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  Finset.Icc (zo.1 - (h : ℤ)) (zo.1 + (h : ℤ)) ×ˢ
    Finset.Icc (zo.2 - (h : ℤ)) (zo.2 + (h : ℤ))

/-- The paper's eight regions 𝓢₁,…,𝓢₈. Lean index `i` is one less than the printed index. -/
def region (h : ℕ) (zo : ℤ × ℤ) (i : Fin 8) : Set (ℤ × ℤ) :=
  fun z =>
    match i.val with
    | 0 => zo.1 + h < z.1 ∧ zo.2 + h < z.2
    | 1 => zo.1 + h < z.1 ∧ zo.2 - h ≤ z.2 ∧ z.2 ≤ zo.2 + h
    | 2 => zo.1 + h < z.1 ∧ z.2 < zo.2 - h
    | 3 => zo.1 - h ≤ z.1 ∧ z.1 ≤ zo.1 + h ∧ z.2 < zo.2 - h
    | 4 => z.1 < zo.1 - h ∧ z.2 < zo.2 - h
    | 5 => z.1 < zo.1 - h ∧ zo.2 - h ≤ z.2 ∧ z.2 ≤ zo.2 + h
    | 6 => z.1 < zo.1 - h ∧ zo.2 + h < z.2
    | _ => zo.1 - h ≤ z.1 ∧ z.1 ≤ zo.1 + h ∧ zo.2 + h < z.2

/-- The head of the paper's arrow aⁱ(z), with zero-based Lean index. -/
def arrowHead (h : ℕ) (i : Fin 8) (z : ℤ × ℤ) : ℤ × ℤ :=
  match i.val with
  | 0 => (z.1 - h, z.2 - h)
  | 1 => (z.1 - h, z.2)
  | 2 => (z.1 - h, z.2 + h)
  | 3 => (z.1, z.2 + h)
  | 4 => (z.1 + h, z.2 + h)
  | 5 => (z.1 + h, z.2)
  | 6 => (z.1 + h, z.2 - h)
  | _ => (z.1, z.2 - h)

/-- The unique region index for a customer outside 𝓘(zₒ). Its value inside 𝓘(zₒ)
is immaterial because the magnet rule handles that case first. -/
def regionIndex (h : ℕ) (zo zc : ℤ × ℤ) : Fin 8 :=
  if zo.1 + h < zc.1 then
    if zo.2 + h < zc.2 then 0 else if zc.2 < zo.2 - h then 2 else 1
  else if zc.1 < zo.1 - h then
    if zo.2 + h < zc.2 then 6 else if zc.2 < zo.2 - h then 4 else 5
  else if zo.2 + h < zc.2 then 7 else if zc.2 < zo.2 - h then 3 else 0

/-- Definitions 1–2: a customer inside 𝓘(zₒ) keeps the stall at its origin;
otherwise use the regional arrow, rotating a type-2 arrow that exits 𝓘₀. -/
noncomputable def magnet (k h : ℕ) (zo zc : ℤ × ℤ) : ℤ × ℤ :=
  if zc ∈ smallDiamond h zo then zo
  else
    let zh := arrowHead h (regionIndex h zo zc) zc
    if zo ∈ type1 k h then zh
    else if zh ∈ inner k h then zh
    else if zh.2 < (h : ℤ) ∨ (k : ℤ) - h < zh.2 then (zh.1, zo.2)
    else (zo.1, zh.2)

/-- The customer locations that cause the transition from `zo` to `zd`.
This includes customers in 𝓘(zₒ) in the self-transition, as the count on p. 48 requires. -/
noncomputable def A (k h : ℕ) (zo zd : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  (grid k).filter (fun zc => magnet k h zo zc = zd)

/-- The rendezvous transition matrix, using the paper's uniform law on all `(k+1)²`
customer grid points. -/
noncomputable def P (k h : ℕ) : Matrix (inner k h) (inner k h) ℝ :=
  fun zo zd => ((A k h zo.1 zd.1).card : ℝ) / ((k : ℝ) + 1) ^ 2

end StallEconomy.Magnet


