-- Prove2me | Definitions.Def_QuadStatRE_Main_BasicEncoding
-- name    : QuadStatRE_Main_BasicEncoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:44:43.083144+00:00
-- url     : https://prove2.me/theorems/b8fd212c-a765-41a8-b634-ce56f02214c4
-- title:
--   Construction 1: the basic degree-2 encoding $\mathrm{Enc}_t$ of $f(x,y,z,w)=xyz+w$ and its decoder
-- statement:
--   Let $G=\mathbb F_2^3$ and $f(x,y,z,w)=xyz+w$ (§3.1, p. 17); the hidden triple of an input is $s=(x,y,z)$. An **encoding of $f$** here is an encoder given by an explicit $\mathbb F_2$-polynomial map $\mathbb F_2^4\times\mathbb F_2^\rho\to\mathbb F_2^m$ (a description in the published sense, with input variables $x,y,z,w$) together with a deterministic decoder $\mathbb F_2^m\to\mathbb F_2\cup\{\bot\}$.
--
--   **Construction 1** (p. 17). For an integer $t\ge1$, $\mathrm{Enc}_t:\mathbb F_2^4\times\mathbb F_2^{6+3t}\to\mathbb F_2^{7+t}$ takes $(x,y,z,w)$ and randomness $r\in\mathbb F_2^6$, $R_1,R_2,R_3\in\mathbb F_2^t$. The base part (3.1) is
--   $$a_1=xy+r_1,\ a_2=z+r_2,\ b_1=xr_2+r_3,\ b_2=y+r_4,\ c_1=r_2r_4+r_5,\ c_2=x+r_6,$$
--   $$\tilde c_3=r_5r_6+r_5x+r_3r_4+r_3y+r_1r_2+r_1z+w,$$
--   and the correction part (3.2) is $Q=(1+r_2)R_1+(1+r_4)R_2+(1+r_6)R_3\in\mathbb F_2^t$. The decoder sets $\hat e=1$ if $Q=0$ and $\hat e=0$ otherwise, and outputs $D(\hat e,\cdot)=a_1a_2+b_1b_2+c_1c_2+\tilde c_3+\hat e$. (With $e=r_2r_4r_6$ one has $a_1a_2+b_1b_2+c_1c_2+\tilde c_3+e=xyz+w$.)
--
--   This gadget has negligible correctness error but constant privacy error; the rest of the paper amplifies its privacy.
--
--   **Formalization Note.** Bits are elements of `ZMod 2`. Inputs are indexed $x,y,z,w=0,1,2,3$; tape positions $0,\dots,5$ are $r_1,\dots,r_6$ and position $6+(a t+i)$ is coordinate $i$ of $R_{a+1}$; output coordinates $0,\dots,6$ are $a_1,a_2,b_1,b_2,c_1,c_2,\tilde c_3$ and $7+i$ is $Q_{i+1}$.
-- source:
--   Applebaum, Quadratic Statistical Randomized Encoding for All Functions, STOC 2027 submission (manuscript sha256 000cbf4e…), p. 17, §3.1, Construction 1, (3.1)–(3.2)

import Mathlib
import Definitions.Def_QuadraticRE_Desc

namespace QuadStatRE.Main

open QuadraticRE

/-- The secrets `G = F₂³` (Applebaum, *Quadratic Statistical Randomized Encoding for All Functions*,
STOC 2027 submission, §4, p. 21: "let `G = F₂³`"). -/
abbrev G : Type := Fin 3 → F2

/-- The target `f(x, y, z, w) = xyz + w` of §§3–7 (p. 17); the input is `v = (x, y, z, w)` with
`x = v 0`, `y = v 1`, `z = v 2`, `w = v 3`. -/
def targetF (v : Fin 4 → F2) : F2 := v 0 * v 1 * v 2 + v 3

/-- The hidden triple `s = (x, y, z) ∈ G` of an input `(x, y, z, w)` (§3.2, p. 17). -/
def secretOf (v : Fin 4 → F2) : G := ![v 0, v 1, v 2]

/-- The input `(s, w) = (x, y, z, w)` built from a triple `s ∈ G` and a bit `w`. -/
def mkInput (s : G) (w : F2) : Fin 4 → F2 := ![s 0, s 1, s 2, w]

/-- An encoding of `f(x, y, z, w) = xyz + w` whose encoder is an explicit `F₂`-polynomial map
`F₂⁴ × F₂^ρ → F₂^m` (a description in the published sense, input variables `x, y, z, w`), together with
its deterministic decoder (`none` is `⊥`). -/
structure Enc4 where
  ρ : ℕ
  m : ℕ
  desc : Desc 4 ρ m
  dec : (Fin m → F2) → Option F2

section Basic

variable (t : ℕ)

/-- The input variables `x, y, z, w`. -/
def vx : Fin 4 ⊕ Fin (6 + 3 * t) := .inl 0
def vy : Fin 4 ⊕ Fin (6 + 3 * t) := .inl 1
def vz : Fin 4 ⊕ Fin (6 + 3 * t) := .inl 2
def vw : Fin 4 ⊕ Fin (6 + 3 * t) := .inl 3

/-- The tape variable `r_i`, `i = 1, …, 6`, is tape position `i − 1`. -/
def vr (i : Fin 6) : Fin 4 ⊕ Fin (6 + 3 * t) := .inr (Fin.castAdd (3 * t) i)

/-- The tape variable `(R_a)_i` (`a = 1, 2, 3` as `a = 0, 1, 2`, `i < t`) is tape position
`6 + (a t + i)`. -/
def vR (a : Fin 3) (i : Fin t) : Fin 4 ⊕ Fin (6 + 3 * t) := .inr (Fin.natAdd 6 (finProdFinEquiv (a, i)))

/-- The base part (3.1), p. 17, in the order `a₁, a₂, b₁, b₂, c₁, c₂, c̃₃`:
`a₁ = xy + r₁`, `a₂ = z + r₂`, `b₁ = x r₂ + r₃`, `b₂ = y + r₄`, `c₁ = r₂ r₄ + r₅`, `c₂ = x + r₆`,
`c̃₃ = r₅ r₆ + r₅ x + r₃ r₄ + r₃ y + r₁ r₂ + r₁ z + w`. -/
def basePart : Fin 7 → List (List (Fin 4 ⊕ Fin (6 + 3 * t))) :=
  ![[[vx t, vy t], [vr t 0]],
    [[vz t], [vr t 1]],
    [[vx t, vr t 1], [vr t 2]],
    [[vy t], [vr t 3]],
    [[vr t 1, vr t 3], [vr t 4]],
    [[vx t], [vr t 5]],
    [[vr t 4, vr t 5], [vr t 4, vx t], [vr t 2, vr t 3], [vr t 2, vy t], [vr t 0, vr t 1],
      [vr t 0, vz t], [vw t]]]

/-- The correction part (3.2), p. 17: `Q = (1 + r₂) R₁ + (1 + r₄) R₂ + (1 + r₆) R₃ ∈ F₂^t`,
coordinate `i`. -/
def corrPart (i : Fin t) : List (List (Fin 4 ⊕ Fin (6 + 3 * t))) :=
  [[vR t 0 i], [vr t 1, vR t 0 i], [vR t 1 i], [vr t 3, vR t 1 i], [vR t 2 i], [vr t 5, vR t 2 i]]

/-- Construction 1 (the basic encoding), p. 17: `Enc_t : F₂⁴ × F₂^{6+3t} → F₂^{7+t}`, the base part
(coordinates `0, …, 6`) followed by the correction part `Q` (coordinates `7, …, 6 + t`). -/
def basicDesc : Desc 4 (6 + 3 * t) (7 + t) :=
  ⟨Fin.append (basePart t) (corrPart t)⟩

/-- The decoder of Construction 1, p. 17: "The decoder sets `ê = 1` if `Q` is the all-zero vector and
`0` otherwise, and outputs the value `D(ê, a₁, a₂, b₁, b₂, c₁, c₂, c̃₃) = a₁a₂ + b₁b₂ + c₁c₂ + c̃₃ + ê`".
It never outputs `⊥`. -/
def basicDec (z : Fin (7 + t) → F2) : Option F2 :=
  let a : Fin 7 → F2 := fun j => z (Fin.castAdd t j)
  let ehat : F2 := if ∀ i : Fin t, z (Fin.natAdd 7 i) = 0 then 1 else 0
  some (a 0 * a 1 + a 2 * a 3 + a 4 * a 5 + a 6 + ehat)

/-- Construction 1 as an encoding of `f`, with `ρ = 6 + 3t` random bits and `m = 7 + t` output bits. -/
def basicEnc : Enc4 := ⟨6 + 3 * t, 7 + t, basicDesc t, basicDec t⟩

end Basic

end QuadStatRE.Main


