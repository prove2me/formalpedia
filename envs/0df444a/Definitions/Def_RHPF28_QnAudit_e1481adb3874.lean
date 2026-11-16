-- Prove2me | Definitions.Def_RHPF28_QnAudit_e1481adb3874
-- name    : RHPF28_QnAudit_e1481adb3874
-- status  : Definition
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:45:38.051771+00:00
-- url     : https://prove2.me/theorems/25084b39-e0c5-472c-8d6a-c3e04ff43e5c
-- title:
--   Definições auxiliares QnAudit — PF28
-- statement:
--   Para t real e n natural, o peso é t^(n−1) exp(−xt); moment integra o produto desse peso com um núcleo K sobre (0,∞). oldQ e newQ são duas normalizações desse momento, especificadas no código. A subtração n−1 é natural truncada. smallLogBound(k,c,t)=−k/t+(c+1/4)t−log t+log(log(2+1/t²)). Estas definições não identificam o núcleo K nem a família Q com objetos da função zeta; essas identificações e a integrabilidade são obrigações separadas.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandao Bueno. PF28 FINAL §166.1; código original QnAudit. Sem reivindicação de novidade. PHIP-1887 e AXLE_QN_POSITIVIDADE_AUDITORIA; arquivos e hashes no inventário V1.

import Mathlib
open MeasureTheory Set
noncomputable section
namespace QnAudit

def weight (x : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  t ^ (n - 1) * Real.exp (-x * t)

def moment (K : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), weight x n t * K t

def oldQ (K : ℝ → ℝ) (u : ℝ) (n : ℕ) : ℝ :=
  2 ^ n * u ^ (2 * n - 1) * moment K (u ^ 2) n

def newQ (K : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  x ^ n / (Nat.factorial (n - 1) : ℝ) * moment K x n

def smallLogBound (k c t : ℝ) : ℝ :=
  -k / t + (c + 1/4) * t - Real.log t + Real.log (Real.log (2 + 1 / t ^ 2))

end QnAudit


