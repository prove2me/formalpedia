-- Prove2me | Definitions.Def_PolyEulerFlow_compiledField
-- name    : PolyEulerFlow_compiledField
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:19:20.873613+00:00
-- url     : https://prove2.me/theorems/1eb637e0-ef5b-40c8-ac6e-db328decde23
-- title:
--   The compiled polynomial field of §6.3 and its intended initial section
-- statement:
--   The polynomial field of §6.3 (pp.26–27) compiled from a separated affine program with tests $u_1,\dots,u_g$. Its active state has four phase bits $p_i$, four timers $\tau_i$ (indices modulo four), comparators $v_1,\dots,v_g$, data registers $Y\in\mathbb R^m$ and shadow registers $Y^s\in\mathbb R^m$. With
--   $$\beta_\sigma(v)=\prod_{j=1}^{g}\frac{1+\sigma_jv_j}{2},\qquad \mathcal T(Y,v)=\sum_{\sigma\in\{-1,1\}^g}\beta_\sigma(v)(D_\sigma Y+b_\sigma),\qquad \varrho(a)=3a^2-2a^3,\qquad \varepsilon=h^K,$$
--   the field is
--   $$p_i'=\varrho(a_i)-p_i,\quad a_i=p_i+S_i(1-p_i)-E_ip_i,\quad S_i=p_{i-1}\tau_{i-1}^2,\quad E_i=p_{i+1}^8,$$
--   $$\tau_i'=p_i\tau_i(1-\tau_i)+(1-p_i)(\varepsilon-\tau_i),\qquad v_j'=(1-p_3)\tfrac12(v_j-v_j^3)+p_3(u_j(Y,h)-v_j),$$
--   $$(Y^s)'=p_1(\mathcal T(Y,v)-Y^s),\qquad Y'=p_3(Y^s-Y).$$
--   The intended initial section (p.27) is $p=(1,0,0,0)$, $\tau_i=\varepsilon$, $Y=C_0$, $Y^s=Y$, $v_j=u_j(Y,h)$.
--
--   **Formalization Note** The field is defined as a real function of $(h,Z)$; Theorem 14 records that it and the initialization are rational polynomials. The clock part depends only on the clock coordinates and $\varepsilon$, so it is also given as an autonomous field on the eight clock coordinates.
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), §6.3, pp.26–27 (PDF 28–29)

import Definitions.Def_PolyEulerFlow_SeparatedAffineProgram

namespace PolyEulerFlow

/-- Clock coordinates: four phase bits `p_i` (`inl`) and four timers `τ_i` (`inr`). -/
abbrev ClockIdx := Fin 4 ⊕ Fin 4

/-- The clock state, with the sup norm. -/
abbrev ClockState := ClockIdx → ℝ

/-- The coordinates of the compiled system: clock, comparators `v_j`, data `Y`, shadows `Y^s`. -/
abbrev CompiledIdx (m g : ℕ) := ClockIdx ⊕ (Fin g ⊕ (Fin m ⊕ Fin m))

/-- The active state of the compiled system, with the sup norm: `2m + g + 8` coordinates (p.26). -/
abbrev CompiledState (m g : ℕ) := CompiledIdx m g → ℝ

/-- The restoration polynomial `ϱ(a) = 3a² - 2a³` (p.26). -/
def restoration (a : ℝ) : ℝ :=
  3 * a ^ 2 - 2 * a ^ 3

/-- The autonomous clock of §6.3, p.26: indices modulo four,
`p′_i = ϱ(a_i) - p_i`, `a_i = p_i + S_i(1 - p_i) - E_i p_i`, `S_i = p_{i-1} τ²_{i-1}`, `E_i = p⁸_{i+1}`,
`τ′_i = p_i τ_i (1 - τ_i) + (1 - p_i)(ε - τ_i)`.
Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…). -/
noncomputable def clockField (ε : ℝ) (X : ClockState) : ClockState
  | .inl i =>
      restoration (X (.inl i) + X (.inl (i - 1)) * X (.inr (i - 1)) ^ 2 * (1 - X (.inl i))
        - X (.inl (i + 1)) ^ 8 * X (.inl i)) - X (.inl i)
  | .inr i =>
      X (.inl i) * X (.inr i) * (1 - X (.inr i)) + (1 - X (.inl i)) * (ε - X (.inr i))

variable {m g : ℕ}

/-- The clock part of a state. -/
def clockPart (Z : CompiledState m g) : ClockState :=
  fun c => Z (.inl c)

/-- The comparators `v`. -/
def compV (Z : CompiledState m g) : Fin g → ℝ :=
  fun j => Z (.inr (.inl j))

/-- The data registers `Y`. -/
def dataY (Z : CompiledState m g) : Fin m → ℝ :=
  fun i => Z (.inr (.inr (.inl i)))

/-- The shadow registers `Y^s`. -/
def shadowY (Z : CompiledState m g) : Fin m → ℝ :=
  fun i => Z (.inr (.inr (.inr i)))

/-- The phase bit `p_i` of a state of the compiled system. -/
def phaseBit (i : Fin 4) (Z : CompiledState m g) : ℝ :=
  Z (.inl (.inl i))

/-- The multilinear weight `β_σ(v) = Π_j (1 + σ_j v_j)/2` (p.26). -/
noncomputable def selectorWeight (σ : Fin g → Bool) (v : Fin g → ℝ) : ℝ :=
  ∏ j, (1 + (if σ j then 1 else -1) * v j) / 2

/-- The selector `T(Y, v) = Σ_σ β_σ(v)(D_σ Y + b_σ)` (p.26). -/
noncomputable def selector (prog : SeparatedAffineProgram m g) (Y : Fin m → ℝ) (v : Fin g → ℝ) : Fin m → ℝ :=
  ∑ σ : Fin g → Bool, selectorWeight σ v • prog.branch σ Y

/-- The compiled field of §6.3, p.26, at scale `h`, with `ε = h^K`:
`v′_j = (1 - p₃)(1/2)(v_j - v_j³) + p₃(u_j(Y, h) - v_j)`, `(Y^s)′ = p₁(T(Y, v) - Y^s)`, `Y′ = p₃(Y^s - Y)`, plus the clock.
**Formalization Note.** This is a real function; `compiledField_polynomial` in Theorem 14 records that it is a rational polynomial in `(h, Z)`. -/
noncomputable def compiledField (prog : SeparatedAffineProgram m g) (K : ℕ) (h : ℝ) (Z : CompiledState m g) : CompiledState m g
  | .inl c => clockField (h ^ K) (clockPart Z) c
  | .inr (.inl j) =>
      (1 - phaseBit 3 Z) * (1 / 2) * (compV Z j - compV Z j ^ 3)
        + phaseBit 3 Z * (prog.test j (dataY Z) h - compV Z j)
  | .inr (.inr (.inl i)) => phaseBit 3 Z * (shadowY Z i - dataY Z i)
  | .inr (.inr (.inr i)) => phaseBit 1 Z * (selector prog (dataY Z) (compV Z) i - shadowY Z i)

/-- The initial clock `p = (1, 0, 0, 0)`, `τ_i = ε` (p.27). -/
noncomputable def initialClock (ε : ℝ) : ClockState
  | .inl i => if i = 0 then 1 else 0
  | .inr _ => ε

/-- The intended initial section, p.27: the initial clock, `Y = C₀`, `Y^s = Y`, `v_j = u_j(Y, h)`. -/
noncomputable def initState (prog : SeparatedAffineProgram m g) (K : ℕ) (h : ℝ) (C0 : Fin m → ℝ) : CompiledState m g
  | .inl c => initialClock (h ^ K) c
  | .inr (.inl j) => prog.test j C0 h
  | .inr (.inr (.inl i)) => C0 i
  | .inr (.inr (.inr i)) => C0 i

end PolyEulerFlow


