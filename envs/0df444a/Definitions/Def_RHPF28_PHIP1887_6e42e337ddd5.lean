-- Prove2me | Definitions.Def_RHPF28_PHIP1887_6e42e337ddd5
-- name    : RHPF28_PHIP1887_6e42e337ddd5
-- status  : Definition
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:43:40.643471+00:00
-- url     : https://prove2.me/theorems/fac8f094-c106-4273-beb0-15b16ba9a5f5
-- title:
--   Definições auxiliares PHIP1887 — PF28
-- statement:
--   Para y complexo e p,q naturais, define-se o átomo a(y;p,q)=y^p(1−y)^q, sua torre por soma das partes reais, a borda e a diagonal. PositiveAt significa não negatividade em todo x>0; NegativeAt, existência de um valor negativo; Cofinal significa que há índices arbitrariamente grandes. Define-se ainda o operador de Euler z(1−z)d/dz, B(ρ)=−(ρ−1/2)², a coordenada x/(x+B(ρ)) e as somas espectrais correspondentes. São definições abstratas; somabilidade, completude da lista de zeros e hipóteses de sinal pertencem aos teoremas posteriores. A soma totalizada do Lean não fornece convergência por si só.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL §166.1; código original PHIP1887. Sem reivindicação de novidade. PHIP-1887 e AXLE_QN_POSITIVIDADE_AUDITORIA; arquivos e hashes no inventário V1.

import Mathlib
open MeasureTheory Set
noncomputable section
namespace PHIP1887

noncomputable def atom (y : ℂ) (p q : ℕ) : ℂ := y^p * (1-y)^q

noncomputable def tower (y : ℕ → ℂ) (p q : ℕ) : ℝ := ∑' j, (atom (y j) p q).re

noncomputable def border (y : ℕ → ℂ) (n : ℕ) : ℝ := tower y n 0

noncomputable def diagonal (y : ℕ → ℂ) (k : ℕ) : ℝ := tower y k k

def PositiveAt (Q : ℕ → ℝ → ℝ) (k : ℕ) : Prop :=
  ∀ x, 0 < x → 0 ≤ Q k x

def NegativeAt (Q : ℕ → ℝ → ℝ) (k : ℕ) : Prop :=
  ∃ x, 0 < x ∧ Q k x < 0

def Cofinal (S : Set ℕ) : Prop := ∀ K, ∃ k ∈ S, K ≤ k

noncomputable def EulerY (f : ℂ → ℂ) (z : ℂ) : ℂ := z*(1-z)*deriv f z

noncomputable def spectralB (rho : ℂ) : ℂ := -(rho-(1/2:ℂ))^2

noncomputable def zeroCoordinate (x : ℝ) (rho : ℂ) : ℂ :=
  (x:ℂ)/((x:ℂ)+spectralB rho)

noncomputable def spectralTower (rho : ℕ → ℂ) (x : ℝ) (p q : ℕ) : ℝ :=
  tower (fun j => zeroCoordinate x (rho j)) p q

noncomputable def spectralDiagonal (rho : ℕ → ℂ) (k : ℕ) (x : ℝ) : ℝ :=
  spectralTower rho x k k

end PHIP1887


