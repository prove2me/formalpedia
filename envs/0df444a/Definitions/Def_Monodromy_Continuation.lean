-- Prove2me | Definitions.Def_Monodromy_Continuation
-- name    : Monodromy_Continuation
-- status  : Definition
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:19:45.570821+00:00
-- url     : https://prove2.me/theorems/5fbc9cec-cf16-4ff9-bb67-ce165adfbfab
-- title:
--   Coupled Three-Root Continuation, Finite Words and Native Programs
-- statement:
--   Defines the fixed complex fiber of (u,v,z)↦(exp u,exp v,exp z/(uv)) over (exp 1,exp 1,1). Actual lower logarithmic lifts generate the upper lift; five fixed drives and their reversals form finite words, finite-root routing selects word tables, and stopping bits define partial program evaluation. Also supplies integer-label refinement, reversible word constructions, phase-packed stage compilers and first-return execution.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Continuation.lean (file SHA-256 c41996cad30503403fe284de8929124f849aa5fd0aaba5433e5e0d4d36fec912):
--   Monodromy.CoupledContinuation.Punctured at L39-L39 [UTF-8 1417:1465].
--   Monodromy.CoupledContinuation.Point at L40-L40 [UTF-8 1466:1513].
--   Monodromy.CoupledContinuation.Base at L41-L41 [UTF-8 1514:1566].
--   Monodromy.CoupledContinuation.one at L43-L43 [UTF-8 1568:1614].
--   Monodromy.CoupledContinuation.base at L44-L44 [UTF-8 1615:1691].
--   Monodromy.CoupledContinuation.projection at L46-L50 [UTF-8 1693:2073].
--   Monodromy.CoupledContinuation.formula at L52-L55 [UTF-8 2075:2325].
--   Monodromy.CoupledContinuation.Memory at L64-L64 [UTF-8 2580:2628].
--   Monodromy.CoupledContinuation.lowerLeft at L66-L67 [UTF-8 2630:2816].
--   Monodromy.CoupledContinuation.lowerRight at L69-L70 [UTF-8 2818:3005].
--   Monodromy.CoupledContinuation.coherent at L72-L75 [UTF-8 3007:3293].
--   Monodromy.CoupledContinuation.Driver at L77-L83 [UTF-8 3295:3622].
--   Monodromy.CoupledContinuation.Driver.path at L85-L89 [UTF-8 3624:3912].
--   Monodromy.CoupledContinuation.lower at L91-L93 [UTF-8 3914:4250].
--   Monodromy.CoupledContinuation.lower_projects at L95-L97 [UTF-8 4252:4575].
--   Monodromy.CoupledContinuation.lower_start at L99-L101 [UTF-8 4577:4870].
--   Monodromy.CoupledContinuation.lower_ne_zero at L103-L110 [UTF-8 4872:5382].
--   Monodromy.CoupledContinuation.feed at L112-L120 [UTF-8 5384:6006].
--   Monodromy.CoupledContinuation.upperPath at L122-L134 [UTF-8 6008:6634].
--   Monodromy.CoupledContinuation.upper at L136-L138 [UTF-8 6636:6883].
--   Monodromy.CoupledContinuation.upper_projects at L140-L146 [UTF-8 6885:7306].
--   Monodromy.CoupledContinuation.upper_start at L148-L149 [UTF-8 7308:7515].
--   Monodromy.CoupledContinuation.trajectory at L151-L158 [UTF-8 7517:8077].
--   Monodromy.CoupledContinuation.trajectory_start at L160-L165 [UTF-8 8079:8391].
--   Monodromy.CoupledContinuation.trajectory_projects at L167-L181 [UTF-8 8393:9214].
--   Monodromy.CoupledContinuation.execute at L183-L184 [UTF-8 9216:9371].
--   Monodromy.CoupledContinuation.rotorPath at L186-L190 [UTF-8 9373:9701].
--   Monodromy.CoupledContinuation.base_ne_one at L192-L194 [UTF-8 9703:9878].
--   Monodromy.CoupledContinuation.controlTurn at L196-L202 [UTF-8 9880:10188].
--   Monodromy.CoupledContinuation.lower_refl at L204-L210 [UTF-8 10190:10732].
--   Monodromy.CoupledContinuation.controlWitness at L212-L214 [UTF-8 10734:10910].
--   Monodromy.CoupledContinuation.controlWitness_projects at L216-L227 [UTF-8 10912:11598].
--   Monodromy.CoupledContinuation.upper_controlTurn at L229-L233 [UTF-8 11600:11947].
--   Monodromy.CoupledContinuation.execute_controlTurn at L235-L245 [UTF-8 11949:12498].
--   Monodromy.CoupledContinuation.upperRoot at L248-L251 [UTF-8 12501:12788].
--   Monodromy.CoupledContinuation.exp_upperRoot at L253-L258 [UTF-8 12790:13194].
--   Monodromy.CoupledContinuation.prepare at L260-L273 [UTF-8 13196:13943].
--   Monodromy.CoupledContinuation.execute_control_prepare at L275-L284 [UTF-8 13945:14433].
--   Monodromy.CoupledContinuation.leftDriver at L287-L294 [UTF-8 14436:14813].
--   Monodromy.CoupledContinuation.lower_left_prepare at L296-L304 [UTF-8 14815:15383].
--   Monodromy.CoupledContinuation.leftWitness at L306-L312 [UTF-8 15385:15941].
--   Monodromy.CoupledContinuation.leftWitness_projects at L314-L326 [UTF-8 15943:16798].
--   Monodromy.CoupledContinuation.upper_left_prepare at L328-L343 [UTF-8 16800:17856].
--   Monodromy.CoupledContinuation.execute_left_refinement at L345-L367 [UTF-8 17858:19455].
--   Monodromy.CoupledContinuation.A_left at L369-L370 [UTF-8 19457:19565].
--   Monodromy.CoupledContinuation.B_left at L372-L373 [UTF-8 19567:19661].
--   Monodromy.CoupledContinuation.execute_A_left at L375-L378 [UTF-8 19663:19922].
--   Monodromy.CoupledContinuation.execute_B_left at L380-L383 [UTF-8 19924:20231].
--   Monodromy.CoupledContinuation.coupled_curve_unique at L386-L418 [UTF-8 20234:22118].
--   Monodromy.CoupledContinuation.exchangePoint at L421-L422 [UTF-8 22121:22270].
--   Monodromy.CoupledContinuation.exchangeBase at L424-L424 [UTF-8 22272:22345].
--   Monodromy.CoupledContinuation.projection_exchange at L426-L433 [UTF-8 22347:22699].
--   Monodromy.CoupledContinuation.exchange at L435-L439 [UTF-8 22701:22894].
--   Monodromy.CoupledContinuation.exchange_prepare at L441-L448 [UTF-8 22896:23182].
--   Monodromy.CoupledContinuation.Driver.exchange at L450-L456 [UTF-8 23184:23461].
--   Monodromy.CoupledContinuation.exchangedTrajectory at L458-L461 [UTF-8 23463:23777].
--   Monodromy.CoupledContinuation.trajectory_exchange at L463-L475 [UTF-8 23779:24605].
--   Monodromy.CoupledContinuation.execute_exchange at L477-L481 [UTF-8 24607:24969].
--   Monodromy.CoupledContinuation.A_right at L483-L483 [UTF-8 24971:25010].
--   Monodromy.CoupledContinuation.B_right at L485-L485 [UTF-8 25012:25051].
--   Monodromy.CoupledContinuation.execute_A_right at L487-L491 [UTF-8 25053:25348].
--   Monodromy.CoupledContinuation.execute_B_right at L493-L497 [UTF-8 25350:25670].
--   Monodromy.CoupledContinuation.Driver.concat at L505-L521 [UTF-8 25767:26300].
--   Monodromy.CoupledContinuation.Driver.reverse at L523-L528 [UTF-8 26302:26548].
--   Monodromy.CoupledContinuation.Driver.concat_path at L530-L537 [UTF-8 26550:26910].
--   Monodromy.CoupledContinuation.Driver.reverse_reverse at L541-L543 [UTF-8 27007:27134].
--   Monodromy.CoupledContinuation.executionPath at L545-L550 [UTF-8 27136:27493].
--   Monodromy.CoupledContinuation.sequentialPath at L552-L554 [UTF-8 27495:27702].
--   Monodromy.CoupledContinuation.sequentialPath_projects at L556-L563 [UTF-8 27704:28076].
--   Monodromy.CoupledContinuation.execute_driver_trans at L565-L575 [UTF-8 28078:28804].
--   Monodromy.CoupledContinuation.execute_driver_reverse at L577-L589 [UTF-8 28806:29622].
--   Monodromy.CoupledContinuation.execute_after_driver_reverse at L591-L594 [UTF-8 29624:29877].
--   Monodromy.CoupledContinuation.controlRoot at L600-L603 [UTF-8 29955:30211].
--   Monodromy.CoupledContinuation.controlRoot_pow at L605-L620 [UTF-8 30213:31079].
--   Monodromy.CoupledContinuation.controlRoot_prepare at L622-L638 [UTF-8 31081:31839].
--   Monodromy.CoupledContinuation.readControl at L640-L644 [UTF-8 31841:32158].
--   Monodromy.CoupledContinuation.prepare_surjective at L650-L674 [UTF-8 32236:33653].
--   Monodromy.CoupledContinuation.prepare_injective at L676-L690 [UTF-8 33655:34460].
--   Monodromy.CoupledPullback.Punctured at L697-L697 [UTF-8 34535:34583].
--   Monodromy.CoupledPullback.Root at L698-L698 [UTF-8 34584:34624].
--   Monodromy.CoupledPullback.Lower at L699-L699 [UTF-8 34625:34668].
--   Monodromy.CoupledPullback.Point at L700-L700 [UTF-8 34669:34706].
--   Monodromy.CoupledPullback.root_ne_zero at L702-L703 [UTF-8 34708:34812].
--   Monodromy.CoupledPullback.exponential at L705-L705 [UTF-8 34814:34909].
--   Monodromy.CoupledPullback.feed at L707-L709 [UTF-8 34911:35102].
--   Monodromy.CoupledPullback.feed_continuous at L711-L711 [UTF-8 35104:35173].
--   Monodromy.CoupledPullback.toPullback at L713-L719 [UTF-8 35175:35611].
--   Monodromy.CoupledPullback.fromPullback at L721-L722 [UTF-8 35613:35718].
--   Monodromy.CoupledPullback.chart at L724-L748 [UTF-8 35720:36746].
--   Monodromy.CoupledPullback.upperProjection at L750-L754 [UTF-8 36748:37062].
--   Monodromy.CoupledPullback.upperCovering at L756-L757 [UTF-8 37064:37230].
--   Monodromy.CoupledPullback.Base at L764-L764 [UTF-8 37301:37383].
--   Monodromy.CoupledPullback.lowerProjection at L766-L767 [UTF-8 37385:37515].
--   Monodromy.CoupledPullback.lowerCovering at L769-L773 [UTF-8 37517:37811].
--   Monodromy.CoupledPullback.values at L775-L775 [UTF-8 37813:37909].
--   Monodromy.CoupledContinuation.execute_A_left_reverse at L787-L792 [UTF-8 38304:38702].
--   Monodromy.CoupledContinuation.execute_A_right_reverse at L794-L798 [UTF-8 38704:39021].
--   Monodromy.CoupledContinuation.execute_control_reverse at L800-L804 [UTF-8 39023:39356].
--   Monodromy.CoupledContinuation.exampleDriver at L839-L841 [UTF-8 40990:41181].
--   Monodromy.CoupledContinuation.controlRoot_is_root at L890-L907 [UTF-8 43330:44484].
--   Monodromy.CoupledContinuation.routeValue at L909-L914 [UTF-8 44486:44873].
--   Monodromy.CoupledContinuation.routeValue_eq at L916-L926 [UTF-8 44875:45468].
--   Monodromy.CoupledContinuation.continuous_routeValue at L928-L933 [UTF-8 45470:45843].
--   Monodromy.CoupledContinuation.routeValue_ne_zero at L935-L939 [UTF-8 45845:46177].
--   Monodromy.CoupledContinuation.routePath at L941-L955 [UTF-8 46179:47026].
--   Monodromy.CoupledContinuation.routePath_eq at L957-L964 [UTF-8 47028:47402].
--   Monodromy.CoupledContinuation.routeDriver at L966-L980 [UTF-8 47404:48238].
--   Monodromy.CoupledContinuation.Driver.eq_of_paths at L982-L990 [UTF-8 48240:48521].
--   Monodromy.CoupledContinuation.routeDriver_eq at L992-L998 [UTF-8 48523:49038].
--   Monodromy.CoupledContinuation.executeRouted at L1000-L1002 [UTF-8 49040:49239].
--   Monodromy.CoupledContinuation.executeRouted_eq at L1004-L1008 [UTF-8 49241:49566].
--   Monodromy.CoupledContinuation.executeRouted_prepare at L1010-L1017 [UTF-8 49568:50127].
--   Monodromy.CoupledContinuation.restrictedBaseRoot at L1025-L1029 [UTF-8 50224:50493].
--   Monodromy.CoupledContinuation.restrictedBase at L1031-L1031 [UTF-8 50495:50587].
--   Monodromy.CoupledContinuation.Driver.restrictedPath at L1033-L1036 [UTF-8 50589:50909].
--   Monodromy.CoupledContinuation.forgetBase at L1038-L1040 [UTF-8 50911:51148].
--   Monodromy.CoupledContinuation.lower_mem at L1045-L1054 [UTF-8 51263:51797].
--   Monodromy.CoupledContinuation.lower_state_mem at L1056-L1063 [UTF-8 51799:52174].
--   Monodromy.CoupledContinuation.restrictedState at L1065-L1068 [UTF-8 52176:52466].
--   Monodromy.CoupledContinuation.forgetPoint at L1070-L1072 [UTF-8 52468:52666].
--   Monodromy.CoupledContinuation.intermediateCurve at L1076-L1083 [UTF-8 52774:53424].
--   Monodromy.CoupledContinuation.restrictedTrajectory at L1085-L1093 [UTF-8 53426:54089].
--   Monodromy.CoupledContinuation.restrictedTrajectory_start at L1098-L1104 [UTF-8 54252:54600].
--   Monodromy.CoupledContinuation.restricted_upper_projection at L1109-L1121 [UTF-8 54761:55475].
--   Monodromy.CoupledContinuation.restricted_lower_projection at L1123-L1132 [UTF-8 55477:56086].
--   Monodromy.CoupledContinuation.restrictedState_over_base at L1134-L1139 [UTF-8 56088:56541].
--   Monodromy.CoupledContinuation.intermediatePath at L1148-L1157 [UTF-8 57020:57540].
--   Monodromy.CoupledContinuation.projection_period_shift at L1192-L1199 [UTF-8 59018:59454].
--   Monodromy.CoupledContinuation.controlDeck at L1201-L1204 [UTF-8 59456:59760].
--   Monodromy.CoupledContinuation.controlDeck_values at L1206-L1207 [UTF-8 59762:59928].
--   Monodromy.CoupledContinuation.controlDeck_prepare at L1209-L1217 [UTF-8 59930:60318].
--   Monodromy.CoupledContinuation.execute_controlDeck at L1219-L1241 [UTF-8 60320:61730].
--   Monodromy.CoupledContinuation.controlRoot_controlDeck at L1243-L1251 [UTF-8 61732:62146].
--   Monodromy.CoupledContinuation.root_prepare at L1257-L1261 [UTF-8 62212:62549].
--   Monodromy.CoupledContinuation.SendsRootCells at L1263-L1266 [UTF-8 62551:62906].
--   Monodromy.CoupledContinuation.MatchesRootCells at L1268-L1272 [UTF-8 62908:63281].
--   Monodromy.CoupledContinuation.matchesRootCells_of_sends at L1274-L1306 [UTF-8 63283:65119].
--   Monodromy.CoupledContinuation.reindexedReverse at L1308-L1310 [UTF-8 65121:65390].
--   Monodromy.CoupledContinuation.permuted_routed_left_inverse at L1312-L1323 [UTF-8 65392:66129].
--   Monodromy.CoupledContinuation.permuted_routed_right_inverse at L1325-L1340 [UTF-8 66131:67158].
--   Monodromy.CoupledContinuation.permutedRoutedEquiv at L1342-L1350 [UTF-8 67160:67808].
--   Monodromy.CoupledContinuation.reverseTable at L1401-L1402 [UTF-8 70692:70829].
--   Monodromy.CoupledContinuation.routedEquiv at L1419-L1423 [UTF-8 71937:72276].
--   Monodromy.CoupledContinuation.Driver.executionEquiv at L1434-L1438 [UTF-8 72773:72998].
--   Monodromy.CoupledContinuation.feedbackEquiv at L1440-L1444 [UTF-8 73000:73394].
--   Monodromy.CoupledContinuation.controlRoot_A_left at L1463-L1466 [UTF-8 74580:74866].
--   Monodromy.CoupledContinuation.controlRoot_A_right at L1468-L1471 [UTF-8 74868:75157].
--   Monodromy.CoupledContinuation.shiftTable at L1473-L1474 [UTF-8 75159:75293].
--   Monodromy.CoupledContinuation.shiftTable_preserves at L1482-L1485 [UTF-8 75529:75769].
--   Monodromy.CoupledContinuation.shiftFeedback at L1487-L1487 [UTF-8 75771:75866].
--   Monodromy.CoupledContinuation.Gate at L1531-L1533 [UTF-8 77698:77836].
--   Monodromy.CoupledContinuation.Gate.driver at L1535-L1540 [UTF-8 77838:77991].
--   Monodromy.CoupledContinuation.Word at L1542-L1543 [UTF-8 77993:78090].
--   Monodromy.CoupledContinuation.idle at L1545-L1550 [UTF-8 78092:78308].
--   Monodromy.CoupledContinuation.execute_idle at L1552-L1559 [UTF-8 78310:78718].
--   Monodromy.CoupledContinuation.Word.driver at L1561-L1564 [UTF-8 78720:78888].
--   Monodromy.CoupledContinuation.Word.atom at L1566-L1566 [UTF-8 78890:78973].
--   Monodromy.CoupledContinuation.Word.control at L1568-L1570 [UTF-8 78975:79131].
--   Monodromy.CoupledContinuation.execute_word_nil at L1572-L1572 [UTF-8 79133:79237].
--   Monodromy.CoupledContinuation.execute_word_cons at L1574-L1577 [UTF-8 79239:79527].
--   Monodromy.CoupledContinuation.execute_word_append at L1584-L1591 [UTF-8 79803:80274].
--   Monodromy.CoupledContinuation.execute_repeat_control at L1593-L1605 [UTF-8 80276:80969].
--   Monodromy.CoupledContinuation.execute_repeat_control_reverse at L1607-L1619 [UTF-8 80971:81678].
--   Monodromy.CoupledContinuation.execute_control_word at L1621-L1628 [UTF-8 81680:82057].
--   Monodromy.CoupledContinuation.Program at L1645-L1648 [UTF-8 82775:82956].
--   Monodromy.CoupledContinuation.Program.advance at L1654-L1655 [UTF-8 83018:83163].
--   Monodromy.CoupledContinuation.Program.haltSignal at L1657-L1661 [UTF-8 83165:83503].
--   Monodromy.CoupledContinuation.Program.step at L1663-L1664 [UTF-8 83505:83654].
--   Monodromy.CoupledContinuation.Program.eval at L1666-L1667 [UTF-8 83656:83755].
--   Monodromy.CoupledContinuation.Program.advance_prepare at L1669-L1673 [UTF-8 83757:84169].
--   Monodromy.CoupledContinuation.Word.inverse at L1704-L1707 [UTF-8 85392:85595].
--   Monodromy.CoupledContinuation.Program.runDriver at L1793-L1799 [UTF-8 89531:89960].
--   Monodromy.ReversibleControl.Guard at L1880-L1881 [UTF-8 93919:94046].
--   Monodromy.ReversibleControl.enabled at L1883-L1889 [UTF-8 94048:94374].
--   Monodromy.ReversibleControl.zeroGate at L1891-L1891 [UTF-8 94376:94464].
--   Monodromy.ReversibleControl.zeroWord at L1893-L1896 [UTF-8 94466:94727].
--   Monodromy.ReversibleControl.execute_zeroGate at L1898-L1905 [UTF-8 94729:95166].
--   Monodromy.ReversibleControl.execute_zeroGate_reverse at L1907-L1913 [UTF-8 95168:95651].
--   Monodromy.ReversibleControl.repeat_forward at L1915-L1926 [UTF-8 95653:96449].
--   Monodromy.ReversibleControl.repeat_backward at L1928-L1939 [UTF-8 96451:97262].
--   Monodromy.ReversibleControl.execute_zeroWord at L1941-L1949 [UTF-8 97264:97712].
--   Monodromy.ReversibleControl.guardWord at L1951-L1956 [UTF-8 97714:98053].
--   Monodromy.ReversibleControl.execute_guardWord at L1958-L1969 [UTF-8 98055:98789].
--   Monodromy.ReversibleControl.table at L1987-L1988 [UTF-8 99472:99632].
--   Monodromy.ReversibleControl.program at L1990-L1992 [UTF-8 99634:99862].
--   Monodromy.ReversibleControl.advance_prepare at L1998-L2013 [UTF-8 100129:101058].
--   Monodromy.ReversibleControl.inverse_prepare at L2015-L2023 [UTF-8 101060:101658].
--   Monodromy.ReversibleControl.prepared_residue_induction at L2025-L2039 [UTF-8 101660:102608].
--   Monodromy.ReversibleControl.inverse at L2041-L2047 [UTF-8 102610:103106].
--   Monodromy.ReversibleControl.executionEquiv at L2078-L2084 [UTF-8 104651:105001].
--   Monodromy.ReversibleControl.swap at L2086-L2087 [UTF-8 105003:105151].
--   Monodromy.ReversibleMemory.memoryGate at L2102-L2102 [UTF-8 105611:105693].
--   Monodromy.ReversibleMemory.shiftWord at L2104-L2106 [UTF-8 105695:105889].
--   Monodromy.ReversibleMemory.execute_memoryGate at L2108-L2120 [UTF-8 105891:106534].
--   Monodromy.ReversibleMemory.execute_memoryGate_reverse at L2122-L2134 [UTF-8 106536:107227].
--   Monodromy.ReversibleMemory.repeat_forward at L2136-L2147 [UTF-8 107229:108073].
--   Monodromy.ReversibleMemory.repeat_backward at L2149-L2160 [UTF-8 108075:108934].
--   Monodromy.ReversibleMemory.execute_shiftWord at L2162-L2170 [UTF-8 108936:109417].
--   Monodromy.ReversibleMemory.memoryWord at L2172-L2173 [UTF-8 109419:109590].
--   Monodromy.ReversibleMemory.execute_memoryWord at L2175-L2178 [UTF-8 109592:109863].
--   Monodromy.ReversibleMemory.controlRoot_memoryWord at L2188-L2192 [UTF-8 110178:110617].
--   Monodromy.ReversibleMemory.memoryWord_inverse at L2194-L2199 [UTF-8 110619:110952].
--   Monodromy.ReversibleMemory.negate at L2203-L2204 [UTF-8 110995:111124].
--   Monodromy.ReversibleMemory.program at L2206-L2208 [UTF-8 111126:111341].
--   Monodromy.ReversibleMemory.advance_of_root at L2221-L2224 [UTF-8 111971:112350].
--   Monodromy.ReversibleMemory.inverse at L2226-L2234 [UTF-8 112352:113018].
--   Monodromy.ReversibleMemory.negate_negate at L2236-L2239 [UTF-8 113020:113178].
--   Monodromy.ReversibleMemory.executionEquiv at L2241-L2247 [UTF-8 113180:113468].
--   Monodromy.CoupledContinuation.Labels at L2261-L2262 [UTF-8 113752:113880].
--   Monodromy.CoupledContinuation.Labels.prepare at L2264-L2264 [UTF-8 113882:113999].
--   Monodromy.CoupledContinuation.Gate.evalInt at L2266-L2274 [UTF-8 114001:114579].
--   Monodromy.CoupledContinuation.Word.evalInt at L2276-L2278 [UTF-8 114581:114745].
--   Monodromy.CoupledContinuation.Gate.execute_evalInt at L2280-L2317 [UTF-8 114747:117039].
--   Monodromy.CoupledContinuation.Word.execute_evalInt at L2319-L2326 [UTF-8 117041:117456].
--   Monodromy.CoupledContinuation.Program.indexInt at L2332-L2336 [UTF-8 117518:117868].
--   Monodromy.CoupledContinuation.Program.nextInt at L2338-L2339 [UTF-8 117870:118001].
--   Monodromy.CoupledContinuation.Program.haltInt at L2341-L2342 [UTF-8 118003:118109].
--   Monodromy.CoupledContinuation.Program.stepInt at L2344-L2345 [UTF-8 118111:118259].
--   Monodromy.CoupledContinuation.Program.evalInt at L2347-L2348 [UTF-8 118261:118366].
--   Monodromy.CoupledContinuation.Program.indexInt_cast at L2350-L2352 [UTF-8 118368:118569].
--   Monodromy.CoupledContinuation.Program.control_decomposition at L2354-L2357 [UTF-8 118571:118772].
--   Monodromy.CoupledContinuation.Program.advance_prepareInt at L2359-L2364 [UTF-8 118774:119151].
--   Monodromy.StagedProgram.pack at L2418-L2420 [UTF-8 121147:121355].
--   Monodromy.StagedProgram.scaleAtom at L2422-L2425 [UTF-8 121357:121502].
--   Monodromy.StagedProgram.scaleWord at L2427-L2429 [UTF-8 121504:121628].
--   Monodromy.StagedProgram.eval_append at L2431-L2436 [UTF-8 121630:121955].
--   Monodromy.StagedProgram.repeat_shear at L2438-L2449 [UTF-8 121957:122511].
--   Monodromy.StagedProgram.scaleAtom_eval at L2451-L2488 [UTF-8 122513:124138].
--   Monodromy.StagedProgram.scaleWord_eval at L2490-L2497 [UTF-8 124140:124512].
--   Monodromy.StagedProgram.execute_scaleWord at L2499-L2502 [UTF-8 124514:124816].
--   Monodromy.StagedProgram.labelsEquiv at L2504-L2505 [UTF-8 124818:124935].
--   Monodromy.StagedProgram.packing at L2509-L2532 [UTF-8 124999:126424].
--   Monodromy.StagedProgram.packedEquiv at L2534-L2536 [UTF-8 126426:126575].
--   Monodromy.StagedProgram.embed at L2538-L2538 [UTF-8 126577:126668].
--   Monodromy.StagedProgram.embed_prepare at L2540-L2544 [UTF-8 126670:126968].
--   Monodromy.StagedProgram.address at L2546-L2547 [UTF-8 126970:127098].
--   Monodromy.StagedProgram.address_val at L2549-L2554 [UTF-8 127100:127348].
--   Monodromy.StagedProgram.clock at L2556-L2557 [UTF-8 127350:127438].
--   Monodromy.StagedProgram.compile at L2559-L2564 [UTF-8 127440:127785].
--   Monodromy.StagedProgram.compile_table at L2566-L2571 [UTF-8 127787:128124].
--   Monodromy.StagedProgram.execute_stageWord at L2573-L2583 [UTF-8 128126:128670].
--   Monodromy.StagedProgram.advance_prepare at L2585-L2604 [UTF-8 128672:129701].
--   Monodromy.StagedProgram.advance_embed at L2606-L2617 [UTF-8 129703:130476].
--   Monodromy.StagedProgram.backClock at L2698-L2700 [UTF-8 134506:134689].
--   Monodromy.StagedProgram.compileReverse at L2702-L2708 [UTF-8 134691:135090].
--   Monodromy.StagedProgram.compileReverse_table at L2710-L2716 [UTF-8 135092:135493].
--   Monodromy.StagedProgram.execute_reverseWord at L2718-L2732 [UTF-8 135495:136338].
--   Monodromy.StagedProgram.reverse_advance_prepare at L2734-L2754 [UTF-8 136340:137471].
--   Monodromy.StagedProgram.reverse_advance_embed at L2756-L2769 [UTF-8 137473:138393].
--   Monodromy.StagedProgram.left_inverse at L2771-L2779 [UTF-8 138395:139010].
--   Monodromy.StagedProgram.right_inverse at L2781-L2789 [UTF-8 139012:139630].
--   Monodromy.StagedProgram.executionEquiv at L2791-L2798 [UTF-8 139632:140156].
--   Monodromy.StagedProgram.markedCompile at L2815-L2821 [UTF-8 140695:141061].
--   Monodromy.StagedProgram.PhaseBoundary at L2895-L2896 [UTF-8 145358:145519].
--   Monodromy.ReversibleReturn.FirstReturn at L3003-L3006 [UTF-8 150850:151226].
--   Monodromy.CoupledContinuation.Program.boundaryInverse at L3065-L3067 [UTF-8 154241:154434].
--   Monodromy.CoupledContinuation.Program.reverseReturn at L3069-L3071 [UTF-8 154436:154676].

-- Generated by Lean-fact skeleton subtraction; original source is frozen in imports/monodromy/source.
module
public import Definitions.Def_Monodromy_Logarithm
public import Definitions.Def_Monodromy_Radix
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Computability.StateTransition
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section


@[expose] public section

/-!
# Coupled analytic continuation

Two retained logarithmic memory roots share one upper control root through
`F(w₁,w₂,z) = (exp w₁, exp w₂, exp z / (w₁*w₂))`. The two actual lower
lifts generate the upper input path. The returned root is the actual upper
lift endpoint; integer labels occur only in preparation and proofs.

The matching lower product covering and upper pullback covering are explicit.
Their actual lifts agree with the complete runtime curves. Five fixed loops
provide memory shifts, zero-conditional control writes and a control shift.
Concatenation and reversal follow from lift uniqueness. A finite power-root
observation routes whole base paths by normalized analytic kernels at returns.

Five oriented loops give a finite word language and finite root-controlled
program tables with internal stopping. Effective semantics and machine
simulation are proved in the subsequent research layers.
-/

noncomputable section

namespace Monodromy.CoupledContinuation

open unitInterval

abbrev Punctured := NestedContinuation.Punctured
abbrev Point := (Punctured × Punctured) × ℂ
abbrev Base := (Punctured × Punctured) × Punctured

abbrev one : Punctured := ⟨1, one_ne_zero⟩
def base : Base := ((NestedContinuation.base, NestedContinuation.base), one)

/-- One three-dimensional projection couples the upper logarithm to both lower roots. -/
def projection (point : Point) : Base :=
  ((NestedContinuation.expCover point.1.1.val, NestedContinuation.expCover point.1.2.val),
    ⟨Complex.exp point.2 / (point.1.1.val * point.1.2.val),
      div_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero point.1.1.property point.1.2.property)⟩)

/-- Its coordinate expression on the open domain of nonzero lower coordinates. -/
def formula (point : (ℂ × ℂ) × ℂ) : (ℂ × ℂ) × ℂ :=
  ((Complex.exp point.1.1, Complex.exp point.1.2),
    Complex.exp point.2 / (point.1.1 * point.1.2))

attribute [local fun_prop] analyticAt_fst analyticAt_snd



abbrev Memory := Transport.Fiber projection base

def lowerLeft (state : Memory) : Transport.Fiber NestedContinuation.expCover NestedContinuation.base :=
  ⟨state.val.1.1.val, congrArg (fun value : Base => value.1.1) state.property⟩

def lowerRight (state : Memory) : Transport.Fiber NestedContinuation.expCover NestedContinuation.base :=
  ⟨state.val.1.2.val, congrArg (fun value : Base => value.1.2) state.property⟩

theorem coherent (state : Memory) :
    Complex.exp state.val.2 = state.val.1.1.val * state.val.1.2.val := by
  have equality := congrArg (fun value : Base => value.2.val) state.property
  exact (div_eq_one_iff_eq (mul_ne_zero state.val.1.1.property state.val.1.2.property)).mp equality

/-- A driver is one based path in each coordinate of the same base space. -/
structure Driver where
  left : Path NestedContinuation.base NestedContinuation.base
  right : Path NestedContinuation.base NestedContinuation.base
  control : Path one one
  left_avoids : ∀ t, left t ≠ one
  right_avoids : ∀ t, right t ≠ one

def Driver.path (driver : Driver) : Path base base where
  toFun t := ((driver.left t, driver.right t), driver.control t)
  continuous_toFun := (driver.left.continuous.prodMk driver.right.continuous).prodMk driver.control.continuous
  source' := by simp [base]
  target' := by simp [base]

/-- Both lower trajectories are actual lifts from their retained root values. -/
def lower (path : Path NestedContinuation.base NestedContinuation.base) (root : Transport.Fiber NestedContinuation.expCover NestedContinuation.base) : C(I, ℂ) :=
  NestedContinuation.covering.liftPath path root.val (path.source.trans root.property.symm)

theorem lower_projects (path : Path NestedContinuation.base NestedContinuation.base) (root : Transport.Fiber NestedContinuation.expCover NestedContinuation.base) :
    NestedContinuation.expCover ∘ lower path root = path :=
  NestedContinuation.covering.liftPath_lifts path root.val (path.source.trans root.property.symm)

theorem lower_start (path : Path NestedContinuation.base NestedContinuation.base) (root : Transport.Fiber NestedContinuation.expCover NestedContinuation.base) :
    lower path root 0 = root.val :=
  NestedContinuation.covering.liftPath_zero path root.val (path.source.trans root.property.symm)

theorem lower_ne_zero (path : Path NestedContinuation.base NestedContinuation.base) (avoids : ∀ t, path t ≠ one)
    (root : Transport.Fiber NestedContinuation.expCover NestedContinuation.base) (t : I) : lower path root t ≠ 0 := by
  intro zero
  apply avoids t
  calc
    path t = NestedContinuation.expCover (lower path root t) := (congrFun (lower_projects path root) t).symm
    _ = NestedContinuation.expCover 0 := congrArg NestedContinuation.expCover zero
    _ = one := Subtype.ext Complex.exp_zero

def feed (driver : Driver) (state : Memory) : C(I, Punctured) where
  toFun t := ⟨(driver.control t).val *
      (lower driver.left (lowerLeft state) t * lower driver.right (lowerRight state) t),
    mul_ne_zero (driver.control t).property
      (mul_ne_zero (lower_ne_zero driver.left driver.left_avoids (lowerLeft state) t)
        (lower_ne_zero driver.right driver.right_avoids (lowerRight state) t))⟩
  continuous_toFun := ((continuous_subtype_val.comp driver.control.continuous).mul
    ((lower driver.left (lowerLeft state)).continuous.mul
      (lower driver.right (lowerRight state)).continuous)).subtype_mk _

/-- The upper input path is generated by the two actual lower lifts and the third base drive. -/
def upperPath (driver : Driver) (state : Memory) :
    Path (NestedContinuation.expCover state.val.2) (feed driver state 1) where
  toFun := feed driver state
  continuous_toFun := (feed driver state).continuous
  source' := by
    apply Subtype.ext
    change (driver.control 0).val *
      (lower driver.left (lowerLeft state) 0 * lower driver.right (lowerRight state) 0) =
      Complex.exp state.val.2
    rw [driver.control.source, lower_start, lower_start]
    exact (one_mul _).trans (coherent state).symm
  target' := rfl

/-- Upper computation is another actual lift, with no target state supplied. -/
def upper (driver : Driver) (state : Memory) : C(I, ℂ) :=
  NestedContinuation.covering.liftPath (upperPath driver state) state.val.2 (upperPath driver state).source

theorem upper_projects (driver : Driver) (state : Memory) (t : I) :
    Complex.exp (upper driver state t) =
      (driver.control t).val *
        (lower driver.left (lowerLeft state) t * lower driver.right (lowerRight state) t) := by
  have projects := NestedContinuation.covering.liftPath_lifts (upperPath driver state) state.val.2
    (upperPath driver state).source
  exact congrArg Subtype.val (congrFun projects t)

theorem upper_start (driver : Driver) (state : Memory) : upper driver state 0 = state.val.2 :=
  NestedContinuation.covering.liftPath_zero (upperPath driver state) state.val.2 (upperPath driver state).source

def trajectory (driver : Driver) (state : Memory) : C(I, Point) where
  toFun t := ((⟨lower driver.left (lowerLeft state) t,
      lower_ne_zero driver.left driver.left_avoids (lowerLeft state) t⟩,
    ⟨lower driver.right (lowerRight state) t,
      lower_ne_zero driver.right driver.right_avoids (lowerRight state) t⟩), upper driver state t)
  continuous_toFun := (((lower driver.left (lowerLeft state)).continuous.subtype_mk _).prodMk
    ((lower driver.right (lowerRight state)).continuous.subtype_mk _)).prodMk
      (upper driver state).continuous

theorem trajectory_start (driver : Driver) (state : Memory) : trajectory driver state 0 = state.val := by
  apply Prod.ext
  · apply Prod.ext <;> apply Subtype.ext
    · exact lower_start driver.left (lowerLeft state)
    · exact lower_start driver.right (lowerRight state)
  · exact upper_start driver state

/-- The whole three-dimensional trajectory follows the one fixed coupled projection. -/
theorem trajectory_projects (driver : Driver) (state : Memory) (t : I) :
    projection (trajectory driver state t) = driver.path t := by
  apply Prod.ext
  · apply Prod.ext
    · exact congrFun (lower_projects driver.left (lowerLeft state)) t
    · exact congrFun (lower_projects driver.right (lowerRight state)) t
  · apply Subtype.ext
    change Complex.exp (upper driver state t) /
      (lower driver.left (lowerLeft state) t * lower driver.right (lowerRight state) t) =
      (driver.control t).val
    rw [upper_projects]
    exact mul_div_cancel_right₀ _
      (mul_ne_zero (lower_ne_zero driver.left driver.left_avoids (lowerLeft state) t)
        (lower_ne_zero driver.right driver.right_avoids (lowerRight state) t))

def execute (driver : Driver) (state : Memory) : Memory :=
  ⟨trajectory driver state 1, (trajectory_projects driver state 1).trans driver.path.target⟩

def rotorPath : Path one one where
  toFun t := ⟨NestedContinuation.rotor t, NestedContinuation.rotor_ne_zero t⟩
  continuous_toFun := NestedContinuation.continuous_rotor.subtype_mk _
  source' := by apply Subtype.ext; exact NestedContinuation.rotor_zero
  target' := by apply Subtype.ext; exact NestedContinuation.rotor_one

theorem base_ne_one : NestedContinuation.base ≠ one := by
  intro same
  exact NestedContinuation.advanceLoop_avoids_one 0 (NestedContinuation.advanceLoop.source.trans same)

/-- This fixed base loop rotates the control drive and holds both lower inputs fixed. -/
def controlTurn : Driver where
  left := Path.refl NestedContinuation.base
  right := Path.refl NestedContinuation.base
  control := rotorPath
  left_avoids := fun _ => base_ne_one
  right_avoids := fun _ => base_ne_one

theorem lower_refl (root : Transport.Fiber NestedContinuation.expCover NestedContinuation.base) (t : I) :
    lower (Path.refl NestedContinuation.base) root t = root.val := by
  let curve : C(I, ℂ) := ContinuousMap.const I root.val
  have same : curve = lower (Path.refl NestedContinuation.base) root :=
    (NestedContinuation.covering.eq_liftPath_iff' ((Path.refl NestedContinuation.base).source.trans root.property.symm)).mpr
      ⟨by funext u; exact root.property, rfl⟩
  exact congrArg (fun value : C(I, ℂ) => value t) same.symm

 def controlWitness (state : Memory) : C(I, ℂ) where
  toFun t := state.val.2 + (((2 * Real.pi) * (t : ℝ) : ℝ) : ℂ) * Complex.I
  continuous_toFun := by fun_prop

 theorem controlWitness_projects (state : Memory) :
    NestedContinuation.expCover ∘ controlWitness state = upperPath controlTurn state := by
  funext t
  apply Subtype.ext
  change Complex.exp (state.val.2 + (((2 * Real.pi) * (t : ℝ) : ℝ) : ℂ) * Complex.I) =
    NestedContinuation.rotor t *
      (lower (Path.refl NestedContinuation.base) (lowerLeft state) t * lower (Path.refl NestedContinuation.base) (lowerRight state) t)
  rw [Complex.exp_add, lower_refl, lower_refl, coherent]
  rw [show Complex.exp ((((2 * Real.pi) * (t : ℝ) : ℝ) : ℂ) * Complex.I) = NestedContinuation.rotor t from
    (Circle.coe_exp _).symm]
  dsimp only [lowerLeft, lowerRight]
  ring

 theorem upper_controlTurn (state : Memory) : upper controlTurn state = controlWitness state := by
  have same : controlWitness state = upper controlTurn state :=
    (NestedContinuation.covering.eq_liftPath_iff' (upperPath controlTurn state).source).mpr
      ⟨controlWitness_projects state, by simp [controlWitness]⟩
  exact same.symm

/-- The control primitive is proved from its actual upper lift; both memories persist. -/
theorem execute_controlTurn (state : Memory) :
    (execute controlTurn state).val.1 = state.val.1 ∧
      (execute controlTurn state).val.2 = state.val.2 + NestedContinuation.period 1 := by
  constructor
  · apply Prod.ext <;> apply Subtype.ext
    · exact lower_refl (lowerLeft state) 1
    · exact lower_refl (lowerRight state) 1
  · change upper controlTurn state 1 = _
    rw [upper_controlTurn]
    simp [controlWitness, NestedContinuation.period]


/-- The three independent branch labels occur only in preparation and correctness statements. -/
def upperRoot (left right control : ℤ) : ℂ :=
  Complex.log (NestedContinuation.firstRoot left) +
    Complex.log (NestedContinuation.firstRoot right) + NestedContinuation.period control

theorem exp_upperRoot (left right control : ℤ) :
    Complex.exp (upperRoot left right control) =
      NestedContinuation.firstRoot left * NestedContinuation.firstRoot right := by
  rw [upperRoot, Complex.exp_add, Complex.exp_add, NestedContinuation.exp_period,
    Complex.exp_log (NestedContinuation.firstRoot_ne_zero left),
    Complex.exp_log (NestedContinuation.firstRoot_ne_zero right), mul_one]

def prepare (left right control : ℤ) : Memory :=
  ⟨((⟨NestedContinuation.firstRoot left, NestedContinuation.firstRoot_ne_zero left⟩,
    ⟨NestedContinuation.firstRoot right, NestedContinuation.firstRoot_ne_zero right⟩),
      upperRoot left right control), by
    apply Prod.ext
    · apply Prod.ext
      · exact NestedContinuation.exp_firstRoot left
      · exact NestedContinuation.exp_firstRoot right
    · apply Subtype.ext
      change Complex.exp (upperRoot left right control) /
        (NestedContinuation.firstRoot left * NestedContinuation.firstRoot right) = 1
      rw [exp_upperRoot, div_self
        (mul_ne_zero (NestedContinuation.firstRoot_ne_zero left)
          (NestedContinuation.firstRoot_ne_zero right))]⟩

theorem execute_control_prepare (left right control : ℤ) :
    execute controlTurn (prepare left right control) = prepare left right (control + 1) := by
  apply Subtype.ext
  apply Prod.ext
  · exact (execute_controlTurn (prepare left right control)).1
  · rw [(execute_controlTurn (prepare left right control)).2]
    change upperRoot left right control + NestedContinuation.period 1 =
      upperRoot left right (control + 1)
    simp [upperRoot, NestedContinuation.period]
    ring


/-- The same fixed lower loop can act on the left memory while the other base coordinates rest. -/
def leftDriver (path : Path NestedContinuation.base NestedContinuation.base)
    (avoids : ∀ t, path t ≠ one) : Driver where
  left := path
  right := Path.refl NestedContinuation.base
  control := Path.refl one
  left_avoids := avoids
  right_avoids := fun _ => base_ne_one

 theorem lower_left_prepare (path : Path NestedContinuation.base NestedContinuation.base)
    (left right control : ℤ) :
    lower path (lowerLeft (prepare left right control)) =
      NestedContinuation.firstRaw path (NestedContinuation.prepare left control) :=
  (NestedContinuation.covering.eq_liftPath_iff'
    (path.source.trans (NestedContinuation.prepare left control).property.symm)).mpr
    ⟨lower_projects path (lowerLeft (prepare left right control)), by
      rw [lower_start]
      exact (NestedContinuation.exp_secondRoot left control).symm⟩

/-- A proof witness reuses the already verified nested lift; it is absent from execution. -/
 def leftWitness (path : Path NestedContinuation.base NestedContinuation.base)
    (avoids : ∀ t, path t ≠ one) (left right control : ℤ) : C(I, ℂ) where
  toFun t := NestedContinuation.secondRaw path avoids
    (NestedContinuation.prepare left control) t + Complex.log (NestedContinuation.firstRoot right)
  continuous_toFun := (NestedContinuation.secondRaw path avoids
    (NestedContinuation.prepare left control)).continuous.add continuous_const

 theorem leftWitness_projects (path : Path NestedContinuation.base NestedContinuation.base)
    (avoids : ∀ t, path t ≠ one) (left right control : ℤ) :
    NestedContinuation.expCover ∘ leftWitness path avoids left right control =
      upperPath (leftDriver path avoids) (prepare left right control) := by
  funext t
  apply Subtype.ext
  change Complex.exp (NestedContinuation.secondRaw path avoids
      (NestedContinuation.prepare left control) t + Complex.log (NestedContinuation.firstRoot right)) =
    (1 : ℂ) * (lower path (lowerLeft (prepare left right control)) t *
      lower (Path.refl NestedContinuation.base) (lowerRight (prepare left right control)) t)
  rw [Complex.exp_add, Complex.exp_log (NestedContinuation.firstRoot_ne_zero right),
    NestedContinuation.secondRaw_exp, one_mul, lower_refl, lower_left_prepare]
  rfl

 theorem upper_left_prepare (path : Path NestedContinuation.base NestedContinuation.base)
    (avoids : ∀ t, path t ≠ one) (left right control : ℤ) :
    upper (leftDriver path avoids) (prepare left right control) = leftWitness path avoids left right control := by
  have same : leftWitness path avoids left right control =
      upper (leftDriver path avoids) (prepare left right control) :=
    (NestedContinuation.covering.eq_liftPath_iff'
      (upperPath (leftDriver path avoids) (prepare left right control)).source).mpr
      ⟨leftWitness_projects path avoids left right control, by
        change NestedContinuation.secondRaw path avoids
          (NestedContinuation.prepare left control) 0 + Complex.log (NestedContinuation.firstRoot right) =
          upperRoot left right control
        rw [NestedContinuation.secondRaw_start]
        change NestedContinuation.secondRoot left control + Complex.log (NestedContinuation.firstRoot right) = _
        unfold NestedContinuation.secondRoot upperRoot
        ring⟩
  exact same.symm

/-- A native nested-loop action lifts to the coupled space with the opposite memory retained. -/
theorem execute_left_refinement (path : Path NestedContinuation.base NestedContinuation.base)
    (avoids : ∀ t, path t ≠ one) (left right control nextLeft nextControl : ℤ)
    (result : NestedContinuation.execute path avoids (NestedContinuation.prepare left control) =
      NestedContinuation.prepare nextLeft nextControl) :
    execute (leftDriver path avoids) (prepare left right control) = prepare nextLeft right nextControl := by
  have endpoint := congrArg (fun state : NestedContinuation.Memory => state.val) result
  change NestedContinuation.secondRaw path avoids (NestedContinuation.prepare left control) 1 =
    NestedContinuation.secondRoot nextLeft nextControl at endpoint
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext <;> apply Subtype.ext
    · change lower path (lowerLeft (prepare left right control)) 1 = NestedContinuation.firstRoot nextLeft
      rw [lower_left_prepare, ← NestedContinuation.secondRaw_exp path avoids
        (NestedContinuation.prepare left control) 1, endpoint, NestedContinuation.exp_secondRoot]
    · exact lower_refl (lowerRight (prepare left right control)) 1
  · change upper (leftDriver path avoids) (prepare left right control) 1 = upperRoot nextLeft right nextControl
    rw [upper_left_prepare]
    change NestedContinuation.secondRaw path avoids (NestedContinuation.prepare left control) 1 +
      Complex.log (NestedContinuation.firstRoot right) = _
    rw [endpoint]
    unfold NestedContinuation.secondRoot upperRoot
    ring

def A_left : Driver :=
  leftDriver NestedContinuation.advanceLoop NestedContinuation.advanceLoop_avoids_one

def B_left : Driver :=
  leftDriver NestedContinuation.loop NestedContinuation.loop_avoids_one

theorem execute_A_left (left right control : ℤ) :
    execute A_left (prepare left right control) = prepare (left + 1) right control :=
  execute_left_refinement _ _ left right control (left + 1) control
    (NestedContinuation.execute_advance left control)

theorem execute_B_left (left right control : ℤ) :
    execute B_left (prepare left right control) = prepare left right (control + if left = 0 then 1 else 0) :=
  execute_left_refinement _ _ left right control left (control + if left = 0 then 1 else 0)
    (NestedContinuation.execute_prepare left control)


/-- The fixed coupled projection determines every continuous lift from its initial point. -/
theorem coupled_curve_unique (first second : C(I, Point))
    (projects : ∀ t, projection (first t) = projection (second t))
    (starts : first 0 = second 0) : first = second := by
  have left_same : (fun t => (first t).1.1.val) = (fun t => (second t).1.1.val) :=
    NestedContinuation.covering.eq_of_comp_eq
      (by fun_prop) (by fun_prop)
      (funext (fun t => congrArg (fun value : Base => value.1.1) (projects t))) 0
      (congrArg (fun value : Point => value.1.1.val) starts)
  have right_same : (fun t => (first t).1.2.val) = (fun t => (second t).1.2.val) :=
    NestedContinuation.covering.eq_of_comp_eq
      (by fun_prop) (by fun_prop)
      (funext (fun t => congrArg (fun value : Base => value.1.2) (projects t))) 0
      (congrArg (fun value : Point => value.1.2.val) starts)
  have upper_projects : NestedContinuation.expCover ∘ (fun t => (first t).2) =
      NestedContinuation.expCover ∘ (fun t => (second t).2) := by
    funext t
    apply Subtype.ext
    have ratio := congrArg (fun value : Base => value.2.val) (projects t)
    change Complex.exp (first t).2 / ((first t).1.1.val * (first t).1.2.val) =
      Complex.exp (second t).2 / ((second t).1.1.val * (second t).1.2.val) at ratio
    rw [congrFun left_same t, congrFun right_same t] at ratio
    exact (div_left_inj' (mul_ne_zero (second t).1.1.property (second t).1.2.property)).mp ratio
  have upper_same : (fun t => (first t).2) = (fun t => (second t).2) :=
    NestedContinuation.covering.eq_of_comp_eq (by fun_prop) (by fun_prop) upper_projects 0
      (congrArg (fun value : Point => value.2) starts)
  apply ContinuousMap.ext
  intro t
  apply Prod.ext
  · apply Prod.ext <;> apply Subtype.ext
    · exact congrFun left_same t
    · exact congrFun right_same t
  · exact congrFun upper_same t


/-- Exchange is a relabelling of the two existing memory coordinates. -/
 def exchangePoint (point : Point) : Point := (point.1.swap, point.2)

 def exchangeBase (value : Base) : Base := (value.1.swap, value.2)

 theorem projection_exchange (point : Point) :
    projection (exchangePoint point) = exchangeBase (projection point) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change Complex.exp point.2 / (point.1.2.val * point.1.1.val) =
      Complex.exp point.2 / (point.1.1.val * point.1.2.val)
    rw [mul_comm point.1.2.val point.1.1.val]

 def exchange (state : Memory) : Memory :=
  ⟨exchangePoint state.val, by
    change projection (exchangePoint state.val) = base
    rw [projection_exchange, state.property]
    rfl⟩

 theorem exchange_prepare (left right control : ℤ) :
    exchange (prepare left right control) = prepare right left control := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change upperRoot left right control = upperRoot right left control
    unfold upperRoot
    ring

/-- The same prescribed base paths with their two memory roles exchanged. -/
def Driver.exchange (driver : Driver) : Driver where
  left := driver.right
  right := driver.left
  control := driver.control
  left_avoids := driver.right_avoids
  right_avoids := driver.left_avoids

 def exchangedTrajectory (driver : Driver) (state : Memory) : C(I, Point) where
  toFun t := exchangePoint (trajectory driver state t)
  continuous_toFun := ((trajectory driver state).continuous.fst.snd.prodMk
    (trajectory driver state).continuous.fst.fst).prodMk (trajectory driver state).continuous.snd

 theorem trajectory_exchange (driver : Driver) (state : Memory) :
    trajectory driver.exchange (exchange state) = exchangedTrajectory driver state := by
  apply coupled_curve_unique
  · intro t
    calc
      projection (trajectory driver.exchange (exchange state) t) = driver.exchange.path t :=
        trajectory_projects driver.exchange (exchange state) t
      _ = exchangeBase (driver.path t) := rfl
      _ = projection (exchangePoint (trajectory driver state t)) :=
        ((projection_exchange _).trans (congrArg exchangeBase (trajectory_projects driver state t))).symm
  · change trajectory driver.exchange (exchange state) 0 = exchangePoint (trajectory driver state 0)
    exact (trajectory_start driver.exchange (exchange state)).trans
      (congrArg exchangePoint (trajectory_start driver state).symm)

 theorem execute_exchange (driver : Driver) (state : Memory) :
    execute driver.exchange (exchange state) = exchange (execute driver state) := by
  apply Subtype.ext
  change trajectory driver.exchange (exchange state) 1 = exchangePoint (trajectory driver state 1)
  exact congrArg (fun curve : C(I, Point) => curve 1) (trajectory_exchange driver state)

def A_right : Driver := A_left.exchange

def B_right : Driver := B_left.exchange

theorem execute_A_right (left right control : ℤ) :
    execute A_right (prepare left right control) = prepare left (right + 1) control := by
  have result := execute_exchange A_left (prepare right left control)
  rw [exchange_prepare, execute_A_left, exchange_prepare] at result
  exact result

theorem execute_B_right (left right control : ℤ) :
    execute B_right (prepare left right control) = prepare left right (control + if right = 0 then 1 else 0) := by
  have result := execute_exchange B_left (prepare right left control)
  rw [exchange_prepare, execute_B_left, exchange_prepare] at result
  exact result

end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

open unitInterval

/-- Driver composition concatenates the three fixed base paths. -/
def Driver.concat (first second : Driver) : Driver where
  left := first.left.trans second.left
  right := first.right.trans second.right
  control := first.control.trans second.control
  left_avoids := by
    intro t
    rw [Path.trans_apply]
    split_ifs
    · exact first.left_avoids _
    · exact second.left_avoids _
  right_avoids := by
    intro t
    rw [Path.trans_apply]
    split_ifs
    · exact first.right_avoids _
    · exact second.right_avoids _

def Driver.reverse (driver : Driver) : Driver where
  left := driver.left.symm
  right := driver.right.symm
  control := driver.control.symm
  left_avoids := fun t => driver.left_avoids (σ t)
  right_avoids := fun t => driver.right_avoids (σ t)

theorem Driver.concat_path (first second : Driver) :
    (first.concat second).path = first.path.trans second.path := by
  apply Path.ext
  funext t
  change (((first.left.trans second.left) t, (first.right.trans second.right) t),
    (first.control.trans second.control) t) = (first.path.trans second.path) t
  simp only [Path.trans_apply]
  split_ifs <;> rfl



theorem Driver.reverse_reverse (driver : Driver) : driver.reverse.reverse = driver := by
  cases driver
  simp [Driver.reverse]

/-- The path consists of the actual three-coordinate lift, rather than an endpoint interpolation. -/
def executionPath (driver : Driver) (state : Memory) : Path state.val (execute driver state).val where
  toFun := trajectory driver state
  continuous_toFun := (trajectory driver state).continuous
  source' := trajectory_start driver state
  target' := rfl

def sequentialPath (first second : Driver) (state : Memory) :
    Path state.val (execute second (execute first state)).val :=
  (executionPath first state).trans (executionPath second (execute first state))

theorem sequentialPath_projects (first second : Driver) (state : Memory) (t : I) :
    projection (sequentialPath first second state t) = (first.concat second).path t := by
  unfold sequentialPath
  rw [Driver.concat_path]
  simp only [Path.trans_apply]
  split_ifs
  · exact trajectory_projects first state _
  · exact trajectory_projects second (execute first state) _

/-- Concatenation composes actual coupled execution on the whole retained geometric state. -/
theorem execute_driver_trans (first second : Driver) (state : Memory) :
    execute (first.concat second) state = execute second (execute first state) := by
  apply Subtype.ext
  let joined := sequentialPath first second state
  have same : trajectory (first.concat second) state = joined.toContinuousMap :=
    coupled_curve_unique _ _
      (fun t => (trajectory_projects (first.concat second) state t).trans
        (sequentialPath_projects first second state t).symm)
      ((trajectory_start (first.concat second) state).trans joined.source.symm)
  exact (congrArg (fun curve : C(I, Point) => curve 1) same).trans joined.target

/-- The reverse driver reverses the actual coupled lifted path. -/
theorem execute_driver_reverse (driver : Driver) (state : Memory) :
    execute driver.reverse (execute driver state) = state := by
  apply Subtype.ext
  let backwards := (executionPath driver state).symm
  have projects : ∀ t, projection (backwards t) = driver.reverse.path t := by
    intro t
    exact trajectory_projects driver state (σ t)
  have same : trajectory driver.reverse (execute driver state) = backwards.toContinuousMap :=
    coupled_curve_unique _ _
      (fun t => (trajectory_projects driver.reverse (execute driver state) t).trans (projects t).symm)
      ((trajectory_start driver.reverse (execute driver state)).trans backwards.source.symm)
  exact (congrArg (fun curve : C(I, Point) => curve 1) same).trans backwards.target

theorem execute_after_driver_reverse (driver : Driver) (state : Memory) :
    execute driver (execute driver.reverse state) = state := by
  have reversed := execute_driver_reverse driver.reverse state
  simpa only [Driver.reverse_reverse] using reversed

end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

/-- The upper cover is observed relative to the canonical lower logarithm charts. -/
def controlRoot (degree : ℕ) (state : Memory) : ℂ :=
  Complex.exp ((state.val.2 - Complex.log state.val.1.1.val -
    Complex.log state.val.1.2.val) / (degree : ℂ))

theorem controlRoot_pow (degree : ℕ) [NeZero degree] (state : Memory) :
    controlRoot degree state ^ degree = 1 := by
  have degree_ne : (degree : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne degree
  have normalized : Complex.exp (state.val.2 - Complex.log state.val.1.1.val -
      Complex.log state.val.1.2.val) = 1 := by
    rw [Complex.exp_sub, Complex.exp_sub,
      Complex.exp_log state.val.1.1.property, Complex.exp_log state.val.1.2.property,
      coherent]
    field_simp [state.val.1.1.property, state.val.1.2.property]
  unfold controlRoot
  rw [← Complex.exp_nat_mul]
  have cancel : (degree : ℂ) *
      ((state.val.2 - Complex.log state.val.1.1.val - Complex.log state.val.1.2.val) /
        (degree : ℂ)) = state.val.2 - Complex.log state.val.1.1.val - Complex.log state.val.1.2.val := by
    field_simp [degree_ne]
  rw [cancel, normalized]

theorem controlRoot_prepare (degree : ℕ) [NeZero degree] (left right control : ℤ) :
    controlRoot degree (prepare left right control) =
      (Radix.readRoot degree ((2 * Real.pi) * (control : ℝ)) : ℂ) := by
  change Complex.exp ((upperRoot left right control -
    Complex.log (NestedContinuation.firstRoot left) -
    Complex.log (NestedContinuation.firstRoot right)) / (degree : ℂ)) = _
  have residual : upperRoot left right control -
      Complex.log (NestedContinuation.firstRoot left) -
      Complex.log (NestedContinuation.firstRoot right) = NestedContinuation.period control := by
    unfold upperRoot
    ring
  rw [residual]
  simp only [Radix.readRoot, Circle.coe_exp]
  congr 1
  unfold NestedContinuation.period
  push_cast
  ring

/-- Reading returns an actual root in the finite power covering, without decoding an integer. -/
def readControl (degree : ℕ) [NeZero degree] (state : Memory) : Radix.Tower.Roots degree :=
  ⟨⟨controlRoot degree state, Complex.exp_ne_zero _⟩, by
    apply Subtype.ext
    exact controlRoot_pow degree state⟩

end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

/-- Every root in the entire coupled fiber has exactly three branch labels. -/
theorem prepare_surjective : Function.Surjective
    (fun labels : (ℤ × ℤ) × ℤ => prepare labels.1.1 labels.1.2 labels.2) := by
  intro state
  obtain ⟨left, left_eq⟩ := Complex.exp_eq_exp_iff_exists_int.mp
    (congrArg Subtype.val (lowerLeft state).property)
  obtain ⟨right, right_eq⟩ := Complex.exp_eq_exp_iff_exists_int.mp
    (congrArg Subtype.val (lowerRight state).property)
  have left_value : state.val.1.1.val = NestedContinuation.firstRoot left := left_eq
  have right_value : state.val.1.2.val = NestedContinuation.firstRoot right := right_eq
  have upper_exp : Complex.exp state.val.2 =
      Complex.exp (Complex.log (NestedContinuation.firstRoot left) +
        Complex.log (NestedContinuation.firstRoot right)) := by
    rw [Complex.exp_add, Complex.exp_log (NestedContinuation.firstRoot_ne_zero left),
      Complex.exp_log (NestedContinuation.firstRoot_ne_zero right)]
    simpa only [left_value, right_value] using coherent state
  obtain ⟨control, control_eq⟩ := Complex.exp_eq_exp_iff_exists_int.mp upper_exp
  have upper_value : state.val.2 = upperRoot left right control := control_eq
  refine ⟨((left, right), control), ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext <;> apply Subtype.ext
    · exact left_value.symm
    · exact right_value.symm
  · exact upper_value.symm

theorem prepare_injective : Function.Injective
    (fun labels : (ℤ × ℤ) × ℤ => prepare labels.1.1 labels.1.2 labels.2) := by
  rintro ⟨⟨left, right⟩, control⟩ ⟨⟨left', right'⟩, control'⟩ same
  have left_eq : left = left' := NestedContinuation.firstRoot_injective
    (congrArg (fun state : Memory => state.val.1.1.val) same)
  have right_eq : right = right' := NestedContinuation.firstRoot_injective
    (congrArg (fun state : Memory => state.val.1.2.val) same)
  subst left'
  subst right'
  have upper_eq := congrArg (fun state : Memory => state.val.2) same
  change upperRoot left right control = upperRoot left right control' at upper_eq
  unfold upperRoot at upper_eq
  have control_eq := NestedContinuation.period_injective (add_left_cancel upper_eq)
  subst control'
  rfl

end Monodromy.CoupledContinuation


namespace Monodromy.CoupledPullback

abbrev Punctured := {value : ℂ // value ≠ 0}
abbrev Root := NestedRestricted.firstSet
abbrev Lower := (Root × Root) × Punctured
abbrev Point := (Root × Root) × ℂ

theorem root_ne_zero (root : Root) : root.val ≠ 0 :=
  NestedRestricted.firstSet_nonzero root.property

def exponential (value : ℂ) : Punctured := ⟨Complex.exp value, Complex.exp_ne_zero value⟩

def feed (point : Lower) : Punctured :=
  ⟨point.2.val * (point.1.1.val * point.1.2.val),
    mul_ne_zero point.2.property (mul_ne_zero (root_ne_zero point.1.1) (root_ne_zero point.1.2))⟩

theorem feed_continuous : Continuous feed := by unfold feed; fun_prop

def toPullback (point : Point) : CoverPullback.Space exponential feed :=
  ⟨((point.1, ⟨Complex.exp point.2 / (point.1.1.val * point.1.2.val),
      div_ne_zero (Complex.exp_ne_zero point.2)
        (mul_ne_zero (root_ne_zero point.1.1) (root_ne_zero point.1.2))⟩), point.2), by
    apply Subtype.ext
    exact (div_mul_cancel₀ (Complex.exp point.2)
      (mul_ne_zero (root_ne_zero point.1.1) (root_ne_zero point.1.2))).symm⟩

def fromPullback (point : CoverPullback.Space exponential feed) : Point :=
  (point.val.1.1, point.val.2)

def chart : Point ≃ₜ CoverPullback.Space exponential feed where
  toFun := toPullback
  invFun := fromPullback
  left_inv _ := rfl
  right_inv point := by
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · apply Subtype.ext
        change Complex.exp point.val.2 /
          (point.val.1.1.1.val * point.val.1.1.2.val) = point.val.1.2.val
        have relation := congrArg Subtype.val point.property
        change Complex.exp point.val.2 =
          point.val.1.2.val * (point.val.1.1.1.val * point.val.1.1.2.val) at relation
        rw [relation]
        exact mul_div_cancel_right₀ _
          (mul_ne_zero (root_ne_zero point.val.1.1.1) (root_ne_zero point.val.1.1.2))
    · rfl
  continuous_toFun := by
    have denominator_nonzero : ∀ point : Point, point.1.1.val * point.1.2.val ≠ 0 :=
      fun point => mul_ne_zero (root_ne_zero point.1.1) (root_ne_zero point.1.2)
    unfold toPullback
    fun_prop (disch := aesop)
  continuous_invFun := by unfold fromPullback; fun_prop

/-- The coupled upper relation is a genuine exponential pullback covering. -/
def upperProjection (point : Point) : Lower :=
  (point.1, ⟨Complex.exp point.2 / (point.1.1.val * point.1.2.val),
    div_ne_zero (Complex.exp_ne_zero point.2)
      (mul_ne_zero (root_ne_zero point.1.1) (root_ne_zero point.1.2))⟩)

theorem upperCovering : IsCoveringMap upperProjection :=
  (CoverPullback.covering (p := exponential) Complex.isCoveringMap_exp feed_continuous).comp_homeomorph chart

end Monodromy.CoupledPullback


namespace Monodromy.CoupledPullback

abbrev Base := (NestedRestricted.baseSet × NestedRestricted.baseSet) × Punctured

def lowerProjection : Lower → Base :=
  Prod.map (Prod.map NestedRestricted.firstProjection NestedRestricted.firstProjection) id

/-- The two lower exponential restrictions and the unchanged control coordinate form a cover. -/
theorem lowerCovering : IsCoveringMap lowerProjection :=
  CoverPullback.prodMap
    (CoverPullback.prodMap NestedRestricted.firstCovering NestedRestricted.firstCovering)
    CoverPullback.identity

def values (point : Base) : (ℂ × ℂ) × ℂ := ((point.1.1.val, point.1.2.val), point.2.val)



end Monodromy.CoupledPullback

namespace Monodromy.CoupledContinuation

/-- Reversing a fixed memory loop decrements its branch without a decoded target. -/
theorem execute_A_left_reverse (left right control : ℤ) :
    execute A_left.reverse (prepare left right control) = prepare (left - 1) right control := by
  have result := execute_driver_reverse A_left (prepare (left - 1) right control)
  rw [execute_A_left] at result
  simpa only [sub_add_cancel] using result

theorem execute_A_right_reverse (left right control : ℤ) :
    execute A_right.reverse (prepare left right control) = prepare left (right - 1) control := by
  have result := execute_driver_reverse A_right (prepare left (right - 1) control)
  rw [execute_A_right] at result
  simpa only [sub_add_cancel] using result

theorem execute_control_reverse (left right control : ℤ) :
    execute controlTurn.reverse (prepare left right control) = prepare left right (control - 1) := by
  have result := execute_driver_reverse controlTurn (prepare left right (control - 1))
  rw [execute_control_prepare] at result
  simpa only [sub_add_cancel] using result







/-- This finite word reads each zero branch by the same geometric mechanism. -/
def exampleDriver : Driver :=
  (((A_left.concat B_left).concat B_right).concat A_right.reverse).concat B_right





end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation



attribute [local fun_prop] analyticAt_fst analyticAt_snd



end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

open unitInterval

variable (degree : ℕ) [NeZero degree]

/-- Every native return has a finite root observation; the witness is used only in proofs. -/
theorem controlRoot_is_root (state : Memory) :
    ∃ index : Fin degree, controlRoot degree state = (Radix.omega degree index : ℂ) := by
  obtain ⟨⟨⟨left, right⟩, control⟩, rfl⟩ := prepare_surjective state
  let index : Fin degree := ⟨(control % (degree : ℤ)).toNat, by
    have positive : 0 < (degree : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne degree)
    have lower := Int.emod_nonneg control positive.ne'
    have upper := Int.emod_lt_of_pos control positive
    omega⟩
  have cast : (index.val : ℤ) = control % (degree : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg control (by exact_mod_cast NeZero.ne degree))
  have decomposition : (degree : ℤ) * (control / (degree : ℤ)) + index.val = control := by
    rw [cast]
    exact Int.mul_ediv_add_emod control (degree : ℤ)
  have read := Radix.readRoot_digit degree (control / (degree : ℤ)) index
  rw [decomposition] at read
  exact ⟨index, (controlRoot_prepare degree left right control).trans
    (congrArg (fun value : Circle => (value : ℂ)) read)⟩

/-- Fixed normalized power-cover kernels route an entire base path, not its endpoint. -/
def routeValue {basepoint : Punctured} (paths : Fin degree → Path basepoint basepoint)
    (state : Memory) (t : I) : ℂ :=
  Choice.dispatch (fun value : ℂ => value ^ degree)
    (fun index => (Radix.omega degree index : ℂ))
    (fun index => (paths index t).val) (controlRoot degree state)

theorem routeValue_eq {basepoint : Punctured} (paths : Fin degree → Path basepoint basepoint)
    (state : Memory) (index : Fin degree)
    (observed : controlRoot degree state = (Radix.omega degree index : ℂ)) (t : I) :
    routeValue degree paths state t = (paths index t).val := by
  unfold routeValue
  rw [observed]
  exact Choice.dispatch_root
    (fun first second same => Radix.omega_injective degree (Subtype.ext same))
    (fun first second => (Radix.omega_complex_pow degree first).trans
      (Radix.omega_complex_pow degree second).symm)
    (Radix.omega_regular degree) index

omit [NeZero degree] in
theorem continuous_routeValue {basepoint : Punctured} (paths : Fin degree → Path basepoint basepoint)
    (state : Memory) : Continuous (routeValue degree paths state) := by
  unfold routeValue Choice.dispatch
  exact continuous_finsetSum Finset.univ (fun index _ =>
    continuous_const.mul (continuous_subtype_val.comp (paths index).continuous))

theorem routeValue_ne_zero {basepoint : Punctured} (paths : Fin degree → Path basepoint basepoint)
    (state : Memory) (t : I) : routeValue degree paths state t ≠ 0 := by
  obtain ⟨index, observed⟩ := controlRoot_is_root degree state
  rw [routeValue_eq degree paths state index observed t]
  exact (paths index t).property

/-- The runtime base path is the finite analytic kernel sum over prescribed paths. -/
def routePath {basepoint : Punctured} (paths : Fin degree → Path basepoint basepoint)
    (state : Memory) : Path basepoint basepoint where
  toFun t := ⟨routeValue degree paths state t, routeValue_ne_zero degree paths state t⟩
  continuous_toFun := (continuous_routeValue degree paths state).subtype_mk _
  source' := by
    obtain ⟨index, observed⟩ := controlRoot_is_root degree state
    apply Subtype.ext
    exact (routeValue_eq degree paths state index observed 0).trans
      (congrArg Subtype.val (paths index).source)
  target' := by
    obtain ⟨index, observed⟩ := controlRoot_is_root degree state
    apply Subtype.ext
    exact (routeValue_eq degree paths state index observed 1).trans
      (congrArg Subtype.val (paths index).target)

theorem routePath_eq {basepoint : Punctured} (paths : Fin degree → Path basepoint basepoint)
    (state : Memory) (index : Fin degree)
    (observed : controlRoot degree state = (Radix.omega degree index : ℂ)) :
    routePath degree paths state = paths index := by
  apply Path.ext
  funext t
  apply Subtype.ext
  exact routeValue_eq degree paths state index observed t

/-- One fixed finite table supplies all three coordinate paths; state supplies only its root. -/
def routeDriver (table : Fin degree → Driver) (state : Memory) : Driver where
  left := routePath degree (fun index => (table index).left) state
  right := routePath degree (fun index => (table index).right) state
  control := routePath degree (fun index => (table index).control) state
  left_avoids := by
    intro t
    obtain ⟨index, observed⟩ := controlRoot_is_root degree state
    rw [routePath_eq degree (fun index => (table index).left) state index observed]
    exact (table index).left_avoids t
  right_avoids := by
    intro t
    obtain ⟨index, observed⟩ := controlRoot_is_root degree state
    rw [routePath_eq degree (fun index => (table index).right) state index observed]
    exact (table index).right_avoids t

 theorem Driver.eq_of_paths (first second : Driver)
    (left : first.left = second.left) (right : first.right = second.right)
    (control : first.control = second.control) : first = second := by
  cases first
  cases second
  cases left
  cases right
  cases control
  rfl

theorem routeDriver_eq (table : Fin degree → Driver) (state : Memory) (index : Fin degree)
    (observed : controlRoot degree state = (Radix.omega degree index : ℂ)) :
    routeDriver degree table state = table index := by
  apply Driver.eq_of_paths
  · exact routePath_eq degree (fun index => (table index).left) state index observed
  · exact routePath_eq degree (fun index => (table index).right) state index observed
  · exact routePath_eq degree (fun index => (table index).control) state index observed

/-- Actual continuation executes the internally routed finite table. -/
def executeRouted (table : Fin degree → Driver) (state : Memory) : Memory :=
  execute (routeDriver degree table state) state

theorem executeRouted_eq (table : Fin degree → Driver) (state : Memory) (index : Fin degree)
    (observed : controlRoot degree state = (Radix.omega degree index : ℂ)) :
    executeRouted degree table state = execute (table index) state := by
  unfold executeRouted
  rw [routeDriver_eq degree table state index observed]

/-- Arbitrary integer controls are routed by their finite residue, without decoding it at runtime. -/
theorem executeRouted_prepare (table : Fin degree → Driver) (left right quotient : ℤ)
    (index : Fin degree) :
    executeRouted degree table (prepare left right ((degree : ℤ) * quotient + index.val)) =
      execute (table index) (prepare left right ((degree : ℤ) * quotient + index.val)) := by
  apply executeRouted_eq
  rw [controlRoot_prepare]
  exact congrArg (fun value : Circle => (value : ℂ)) (Radix.readRoot_digit degree quotient index)

end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

open unitInterval

/-- The fixed base point belongs to the twice-punctured base of each lower cover. -/
def restrictedBaseRoot : NestedRestricted.baseSet :=
  ⟨NestedContinuation.base.val, NestedContinuation.base.property, by
    intro equal
    exact base_ne_one (Subtype.ext equal)⟩

def restrictedBase : CoupledPullback.Base := ((restrictedBaseRoot, restrictedBaseRoot), one)

def Driver.restrictedPath (driver : Driver) : Path restrictedBase restrictedBase :=
  ((NestedRestricted.basePath driver.left (fun t equal => driver.left_avoids t (Subtype.ext equal))).prod
    (NestedRestricted.basePath driver.right (fun t equal => driver.right_avoids t (Subtype.ext equal)))).prod
      driver.control

/-- Restriction changes the geometric domain, preserving all base coordinates. -/
def forgetBase (point : CoupledPullback.Base) : Base :=
  ((⟨point.1.1.val, point.1.1.property.1⟩, ⟨point.1.2.val, point.1.2.property.1⟩), point.2)



theorem lower_mem (path : Path NestedContinuation.base NestedContinuation.base)
    (avoids : ∀ t, path t ≠ one)
    (root : Transport.Fiber NestedContinuation.expCover NestedContinuation.base) (t : I) :
    lower path root t ∈ NestedRestricted.firstSet := by
  change Complex.exp (lower path root t) ≠ 0 ∧ Complex.exp (lower path root t) ≠ 1
  refine ⟨Complex.exp_ne_zero _, ?_⟩
  intro equal
  apply avoids t
  apply Subtype.ext
  exact (congrArg Subtype.val (congrFun (lower_projects path root) t)).symm.trans equal

theorem lower_state_mem (root : Transport.Fiber NestedContinuation.expCover NestedContinuation.base) :
    root.val ∈ NestedRestricted.firstSet := by
  change Complex.exp root.val ≠ 0 ∧ Complex.exp root.val ≠ 1
  refine ⟨Complex.exp_ne_zero _, ?_⟩
  intro equal
  apply base_ne_one
  apply Subtype.ext
  exact (congrArg Subtype.val root.property).symm.trans equal

/-- The same retained root triple, carrying only proofs of its covering domains. -/
def restrictedState (state : Memory) : CoupledPullback.Point :=
  ((⟨state.val.1.1.val, lower_state_mem (lowerLeft state)⟩,
    ⟨state.val.1.2.val, lower_state_mem (lowerRight state)⟩), state.val.2)

def forgetPoint (point : CoupledPullback.Point) : Point :=
  ((⟨point.1.1.val, CoupledPullback.root_ne_zero point.1.1⟩,
    ⟨point.1.2.val, CoupledPullback.root_ne_zero point.1.2⟩), point.2)



/-- The actual lower lifts and fixed third base coordinate form the intermediate curve. -/
def intermediateCurve (driver : Driver) (state : Memory) : C(I, CoupledPullback.Lower) where
  toFun t := ((⟨lower driver.left (lowerLeft state) t,
      lower_mem driver.left driver.left_avoids (lowerLeft state) t⟩,
    ⟨lower driver.right (lowerRight state) t,
      lower_mem driver.right driver.right_avoids (lowerRight state) t⟩), driver.control t)
  continuous_toFun := (((lower driver.left (lowerLeft state)).continuous.subtype_mk _).prodMk
    ((lower driver.right (lowerRight state)).continuous.subtype_mk _)).prodMk driver.control.continuous

/-- No curve is prescribed: this wraps the already constructed actual upper lift. -/
def restrictedTrajectory (driver : Driver) (state : Memory) : C(I, CoupledPullback.Point) where
  toFun t := ((⟨lower driver.left (lowerLeft state) t,
      lower_mem driver.left driver.left_avoids (lowerLeft state) t⟩,
    ⟨lower driver.right (lowerRight state) t,
      lower_mem driver.right driver.right_avoids (lowerRight state) t⟩), upper driver state t)
  continuous_toFun := (((lower driver.left (lowerLeft state)).continuous.subtype_mk _).prodMk
    ((lower driver.right (lowerRight state)).continuous.subtype_mk _)).prodMk
      (upper driver state).continuous



theorem restrictedTrajectory_start (driver : Driver) (state : Memory) :
    restrictedTrajectory driver state 0 = restrictedState state := by
  apply Prod.ext
  · apply Prod.ext <;> apply Subtype.ext
    · exact lower_start driver.left (lowerLeft state)
    · exact lower_start driver.right (lowerRight state)
  · exact upper_start driver state



/-- The first geometric arrow projects the actual lifted upper trajectory. -/
theorem restricted_upper_projection (driver : Driver) (state : Memory) (t : I) :
    CoupledPullback.upperProjection (restrictedTrajectory driver state t) = intermediateCurve driver state t := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change Complex.exp (upper driver state t) /
      (lower driver.left (lowerLeft state) t * lower driver.right (lowerRight state) t) =
      (driver.control t).val
    rw [upper_projects]
    exact mul_div_cancel_right₀ _
      (mul_ne_zero (lower_ne_zero driver.left driver.left_avoids (lowerLeft state) t)
        (lower_ne_zero driver.right driver.right_avoids (lowerRight state) t))

/-- The second geometric arrow projects the actual intermediate curve to the fixed driver. -/
theorem restricted_lower_projection (driver : Driver) (state : Memory) (t : I) :
    CoupledPullback.lowerProjection (intermediateCurve driver state t) = driver.restrictedPath t := by
  apply Prod.ext
  · apply Prod.ext <;> apply Subtype.ext
    · exact congrArg (fun value : Punctured => (value : ℂ))
        (congrFun (lower_projects driver.left (lowerLeft state)) t)
    · exact congrArg (fun value : Punctured => (value : ℂ))
        (congrFun (lower_projects driver.right (lowerRight state)) t)
  · rfl

theorem restrictedState_over_base (state : Memory) :
    CoupledPullback.lowerProjection (CoupledPullback.upperProjection (restrictedState state)) = restrictedBase := by
  let driver : Driver := controlTurn
  have first := congrArg CoupledPullback.lowerProjection (restricted_upper_projection driver state 0)
  rw [restrictedTrajectory_start] at first
  exact first.trans ((restricted_lower_projection driver state 0).trans driver.restrictedPath.source)




/-- The intermediate path is the actual generated curve, with its actual endpoints. -/
def intermediatePath (driver : Driver) (state : Memory) :
    Path (CoupledPullback.upperProjection (restrictedState state)) (intermediateCurve driver state 1) where
  toFun := intermediateCurve driver state
  continuous_toFun := (intermediateCurve driver state).continuous
  source' := by
    have first := restricted_upper_projection driver state 0
    rw [restrictedTrajectory_start] at first
    exact first.symm
  target' := rfl





end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

open unitInterval

theorem projection_period_shift (amount : ℤ) (point : Point) :
    projection (point.1, point.2 + NestedContinuation.period amount) = projection point := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change Complex.exp (point.2 + NestedContinuation.period amount) /
      (point.1.1.val * point.1.2.val) = Complex.exp point.2 / (point.1.1.val * point.1.2.val)
    rw [Complex.exp_add, NestedContinuation.exp_period, mul_one]

/-- The intrinsic upper deck action; `controlDeck_eq_control_word` gives its existing executable word. -/
def controlDeck (amount : ℤ) (state : Memory) : Memory :=
  ⟨(state.val.1, state.val.2 + NestedContinuation.period amount),
    (projection_period_shift amount state.val).trans state.property⟩

theorem controlDeck_values (amount : ℤ) (state : Memory) :
    (controlDeck amount state).val = (state.val.1, state.val.2 + NestedContinuation.period amount) := rfl

theorem controlDeck_prepare (amount left right control : ℤ) :
    controlDeck amount (prepare left right control) = prepare left right (control + amount) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change upperRoot left right control + NestedContinuation.period amount =
      upperRoot left right (control + amount)
    simp [upperRoot, NestedContinuation.period]
    ring

/-- Lift uniqueness makes every fixed driver equivariant under the upper deck action. -/
theorem execute_controlDeck (driver : Driver) (amount : ℤ) (state : Memory) :
    execute driver (controlDeck amount state) = controlDeck amount (execute driver state) := by
  let shifted : C(I, Point) :=
    ⟨fun time => ((trajectory driver state time).1,
      (trajectory driver state time).2 + NestedContinuation.period amount),
      (trajectory driver state).continuous.fst.prodMk
        ((trajectory driver state).continuous.snd.add continuous_const)⟩
  have projects : ∀ time, projection (shifted time) = driver.path time := by
    intro time
    exact (projection_period_shift amount (trajectory driver state time)).trans
      (trajectory_projects driver state time)
  have starts : trajectory driver (controlDeck amount state) 0 = shifted 0 := by
    change trajectory driver (controlDeck amount state) 0 =
      ((trajectory driver state 0).1, (trajectory driver state 0).2 + NestedContinuation.period amount)
    rw [trajectory_start, trajectory_start, controlDeck_values]
  have same : trajectory driver (controlDeck amount state) = shifted :=
    coupled_curve_unique _ _
      (fun time => (trajectory_projects driver (controlDeck amount state) time).trans (projects time).symm)
      starts
  apply Subtype.ext
  rw [controlDeck_values]
  exact congrArg (fun curve : C(I, Point) => curve 1) same

/-- A deck shift multiplies every return observation by the same finite-cover phase. -/
theorem controlRoot_controlDeck (degree : ℕ) (amount : ℤ) (state : Memory) :
    controlRoot degree (controlDeck amount state) =
      Complex.exp (NestedContinuation.period amount / (degree : ℂ)) * controlRoot degree state := by
  unfold controlRoot
  rw [controlDeck_values]
  rw [← Complex.exp_add]
  congr 1
  ring

section FiniteRouting

variable (degree : ℕ) [NeZero degree]

 theorem root_prepare (index : Fin degree) (left right : ℤ) :
    controlRoot degree (prepare left right index.val) = (Radix.omega degree index : ℂ) := by
  rw [controlRoot_prepare]
  have root := congrArg (fun value : Circle => (value : ℂ)) (Radix.readRoot_digit degree 0 index)
  simpa only [mul_zero, zero_add] using root

/-- Every selected path has a fixed target observation on its own source cell. -/
def SendsRootCells (table : Fin degree → Driver) (next : Fin degree → Fin degree) : Prop :=
  ∀ index state, controlRoot degree state = (Radix.omega degree index : ℂ) →
    controlRoot degree (execute (table index) state) = (Radix.omega degree (next index) : ℂ)

/-- Exact cell matching includes the preimage condition needed to reverse a routed path. -/
def MatchesRootCells (table : Fin degree → Driver) (next : Fin degree → Fin degree) : Prop :=
  ∀ index state,
    controlRoot degree (execute (table index) state) = (Radix.omega degree (next index) : ℂ) ↔
      controlRoot degree state = (Radix.omega degree index : ℂ)

/-- For these actual lifts, one-sided cell transport is exact by deck equivariance. -/
theorem matchesRootCells_of_sends (table : Fin degree → Driver) (next : Fin degree → Fin degree)
    (sends : SendsRootCells degree table next) : MatchesRootCells degree table next := by
  intro index state
  constructor
  · intro target
    obtain ⟨⟨⟨left, right⟩, control⟩, rfl⟩ := prepare_surjective state
    change controlRoot degree (execute (table index) (prepare left right control)) =
      (Radix.omega degree (next index) : ℂ) at target
    change controlRoot degree (prepare left right control) = (Radix.omega degree index : ℂ)
    let initial := prepare left right (index.val : ℤ)
    let amount : ℤ := control - index.val
    have initial_root : controlRoot degree initial = (Radix.omega degree index : ℂ) :=
      root_prepare degree index left right
    have initial_target := sends index initial initial_root
    have shifted : controlDeck amount initial = prepare left right control := by
      rw [controlDeck_prepare]
      congr 1
      dsimp [amount]
      omega
    have output_phase :
        controlRoot degree (execute (table index) (prepare left right control)) =
          Complex.exp (NestedContinuation.period amount / (degree : ℂ)) *
            controlRoot degree (execute (table index) initial) := by
      rw [← shifted, execute_controlDeck, controlRoot_controlDeck]
    have balance := output_phase.symm.trans target
    rw [initial_target] at balance
    have phase_one : Complex.exp (NestedContinuation.period amount / (degree : ℂ)) = 1 := by
      apply mul_right_cancel₀ (Radix.omega degree (next index)).coe_ne_zero
      simpa only [one_mul] using balance
    rw [← shifted, controlRoot_controlDeck, phase_one, one_mul]
    exact initial_root
  · exact sends index state

/-- Inversion uses the same paths in reverse, indexed by the inverse finite permutation. -/
def reindexedReverse (table : Fin degree → Driver) (permutation : Equiv.Perm (Fin degree)) :
    Fin degree → Driver := fun index => (table (permutation.symm index)).reverse

theorem permuted_routed_left_inverse (table : Fin degree → Driver)
    (permutation : Equiv.Perm (Fin degree))
    (cells : MatchesRootCells degree table permutation) :
    Function.LeftInverse (executeRouted degree (reindexedReverse degree table permutation))
      (executeRouted degree table) := by
  intro state
  obtain ⟨index, observed⟩ := controlRoot_is_root degree state
  have moved := (cells index state).mpr observed
  rw [executeRouted_eq degree table state index observed]
  rw [executeRouted_eq degree (reindexedReverse degree table permutation)
    (execute (table index) state) (permutation index) moved]
  simpa only [reindexedReverse, permutation.symm_apply_apply] using execute_driver_reverse (table index) state

theorem permuted_routed_right_inverse (table : Fin degree → Driver)
    (permutation : Equiv.Perm (Fin degree))
    (cells : MatchesRootCells degree table permutation) :
    Function.RightInverse (executeRouted degree (reindexedReverse degree table permutation))
      (executeRouted degree table) := by
  intro state
  obtain ⟨index, observed⟩ := controlRoot_is_root degree state
  have reversed : controlRoot degree (execute (table (permutation.symm index)).reverse state) =
      (Radix.omega degree (permutation.symm index) : ℂ) := by
    apply (cells (permutation.symm index) _).mp
    rw [execute_after_driver_reverse, permutation.apply_symm_apply]
    exact observed
  rw [executeRouted_eq degree (reindexedReverse degree table permutation) state index observed]
  change executeRouted degree table (execute (table (permutation.symm index)).reverse state) = state
  rw [executeRouted_eq degree table _ (permutation.symm index) reversed]
  exact execute_after_driver_reverse (table (permutation.symm index)) state

/-- A root-permuting table is globally reversible by the existing routed execution kernel. -/
def permutedRoutedEquiv (table : Fin degree → Driver) (permutation : Equiv.Perm (Fin degree))
    (sends : SendsRootCells degree table permutation) : Memory ≃ Memory where
  toFun := executeRouted degree table
  invFun := executeRouted degree (reindexedReverse degree table permutation)
  left_inv := permuted_routed_left_inverse degree table permutation
    (matchesRootCells_of_sends degree table permutation sends)
  right_inv := permuted_routed_right_inverse degree table permutation
    (matchesRootCells_of_sends degree table permutation sends)











end FiniteRouting



def reverseTable (degree : ℕ) (table : Fin degree → Driver) : Fin degree → Driver :=
  reindexedReverse degree table (Equiv.refl _)





def routedEquiv (degree : ℕ) [NeZero degree] (table : Fin degree → Driver)
    (preserves : ∀ index state, controlRoot degree (execute (table index) state) = controlRoot degree state) :
    Memory ≃ Memory :=
  permutedRoutedEquiv degree table (Equiv.refl _)
    (fun index state observed => (preserves index state).trans observed)



def Driver.executionEquiv (driver : Driver) : Memory ≃ Memory where
  toFun := execute driver
  invFun := execute driver.reverse
  left_inv := execute_driver_reverse driver
  right_inv := execute_after_driver_reverse driver

/-- A reversible routed return followed by any fixed actual gate closes the feedback cycle. -/
def feedbackEquiv (degree : ℕ) [NeZero degree] (table : Fin degree → Driver)
    (preserves : ∀ index state, controlRoot degree (execute (table index) state) = controlRoot degree state)
    (gate : Driver) : Memory ≃ Memory :=
  (routedEquiv degree table preserves).trans gate.executionEquiv







theorem controlRoot_A_left (degree : ℕ) [NeZero degree] (state : Memory) :
    controlRoot degree (execute A_left state) = controlRoot degree state := by
  obtain ⟨⟨⟨left, right⟩, control⟩, rfl⟩ := prepare_surjective state
  simp only [execute_A_left, controlRoot_prepare]

theorem controlRoot_A_right (degree : ℕ) [NeZero degree] (state : Memory) :
    controlRoot degree (execute A_right state) = controlRoot degree state := by
  obtain ⟨⟨⟨left, right⟩, control⟩, rfl⟩ := prepare_surjective state
  simp only [execute_A_right, controlRoot_prepare]

/-- A fixed two-entry table of genuine memory-shift paths. -/
def shiftTable : Fin 2 → Driver := Fin.cases A_left (fun _ => A_right)





theorem shiftTable_preserves : ∀ index state,
    controlRoot 2 (execute (shiftTable index) state) = controlRoot 2 state := by
  intro index state
  exact Fin.cases (controlRoot_A_left 2 state) (fun _ => controlRoot_A_right 2 state) index

def shiftFeedback : Memory ≃ Memory := feedbackEquiv 2 shiftTable shiftTable_preserves B_left







end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation



end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

open unitInterval

/-- The finite alphabet consists of the five existing geometric loops. -/
inductive Gate
  | left | right | zeroLeft | zeroRight | control

def Gate.driver : Gate → Driver
  | .left => A_left
  | .right => A_right
  | .zeroLeft => B_left
  | .zeroRight => B_right
  | .control => controlTurn

/-- A Boolean sign means reverse the same actual base path. -/
abbrev Word := List (Gate × Bool)

def idle : Driver where
  left := Path.refl NestedContinuation.base
  right := Path.refl NestedContinuation.base
  control := Path.refl one
  left_avoids := fun _ => base_ne_one
  right_avoids := fun _ => base_ne_one

theorem execute_idle (state : Memory) : execute idle state = state := by
  apply Subtype.ext
  let constant : C(I, Point) := ContinuousMap.const I state.val
  have same : trajectory idle state = constant :=
    coupled_curve_unique _ _
      (fun t => (trajectory_projects idle state t).trans state.property.symm)
      (trajectory_start idle state)
  exact congrArg (fun curve : C(I, Point) => curve 1) same

def Word.driver : Word → Driver
  | [] => idle
  | (gate, backward) :: rest =>
      (if backward then gate.driver.reverse else gate.driver).concat (Word.driver rest)

def Word.atom (gate : Gate) (backward : Bool := false) : Word := [(gate, backward)]

def Word.control : ℤ → Word
  | .ofNat count => List.replicate count (.control, false)
  | .negSucc count => List.replicate (count + 1) (.control, true)

theorem execute_word_nil (state : Memory) : execute (Word.driver []) state = state := execute_idle state

theorem execute_word_cons (gate : Gate) (backward : Bool) (rest : Word) (state : Memory) :
    execute (Word.driver ((gate, backward) :: rest)) state =
      execute (Word.driver rest) (execute (if backward then gate.driver.reverse else gate.driver) state) :=
  execute_driver_trans _ _ _



theorem execute_word_append (first second : Word) (state : Memory) :
    execute (Word.driver (first ++ second)) state =
      execute (Word.driver second) (execute (Word.driver first) state) := by
  induction first generalizing state with
  | nil => simp only [List.nil_append, execute_word_nil]
  | cons atom rest induction_hypothesis =>
      rcases atom with ⟨gate, backward⟩
      rw [List.cons_append, execute_word_cons, execute_word_cons, induction_hypothesis]

theorem execute_repeat_control (count : ℕ) (left right control : ℤ) :
    execute (Word.driver (List.replicate count (Gate.control, false))) (prepare left right control) =
      prepare left right (control + (count : ℤ)) := by
  induction count generalizing control with
  | zero => simp only [List.replicate_zero, execute_word_nil, Nat.cast_zero, add_zero]
  | succ count induction_hypothesis =>
      rw [List.replicate_succ, execute_word_cons]
      change execute (Word.driver (List.replicate count (Gate.control, false)))
        (execute controlTurn (prepare left right control)) = _
      rw [execute_control_prepare, induction_hypothesis]
      congr 1
      push_cast
      ring

theorem execute_repeat_control_reverse (count : ℕ) (left right control : ℤ) :
    execute (Word.driver (List.replicate count (Gate.control, true))) (prepare left right control) =
      prepare left right (control - (count : ℤ)) := by
  induction count generalizing control with
  | zero => simp only [List.replicate_zero, execute_word_nil, Nat.cast_zero, sub_zero]
  | succ count induction_hypothesis =>
      rw [List.replicate_succ, execute_word_cons]
      change execute (Word.driver (List.replicate count (Gate.control, true)))
        (execute controlTurn.reverse (prepare left right control)) = _
      rw [execute_control_reverse, induction_hypothesis]
      congr 1
      push_cast
      ring

theorem execute_control_word (amount left right control : ℤ) :
    execute (Word.driver (Word.control amount)) (prepare left right control) =
      prepare left right (control + amount) := by
  cases amount with
  | ofNat count => exact execute_repeat_control count left right control
  | negSucc count =>
      rw [Word.control, execute_repeat_control_reverse]
      congr 1





end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

/-- A finite program consists only of geometric words and marked stopping roots. -/
structure Program (degree : ℕ) where
  table : Fin degree → Word
  stop : Fin degree → Bool

namespace Program

variable {degree : ℕ} [NeZero degree]

def advance (program : Program degree) (state : Memory) : Memory :=
  executeRouted degree (fun index => Word.driver (program.table index)) state

/-- Stopping reads the same finite cover root through fixed normalized kernels. -/
def haltSignal (program : Program degree) (state : Memory) : ℂ :=
  Choice.dispatch (fun value : ℂ => value ^ degree)
    (fun index => (Radix.omega degree index : ℂ))
    (fun index => if program.stop index then 1 else 0) (controlRoot degree state)

def step (program : Program degree) (state : Memory) : Option Memory :=
  if program.haltSignal state = 1 then none else some (program.advance state)

def eval (program : Program degree) : Memory → Part Memory :=
  StateTransition.eval program.step

theorem advance_prepare (program : Program degree) (left right quotient : ℤ) (index : Fin degree) :
    program.advance (prepare left right ((degree : ℤ) * quotient + index.val)) =
      execute (Word.driver (program.table index))
        (prepare left right ((degree : ℤ) * quotient + index.val)) :=
  executeRouted_prepare degree (fun index => Word.driver (program.table index)) left right quotient index





end Program

end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

/-- An inverse program reverses the word and each oriented geometric loop. -/
def Word.inverse : Word → Word
  | [] => []
  | (gate, backward) :: rest => Word.inverse rest ++ Word.atom gate (!backward)









end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation





end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation



end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation.Program

variable {degree : ℕ} [NeZero degree]

/-- A fixed-length advance prefix. Each next driver uses the preceding actual lift result.
The step/eval hypotheses below certify which prefixes respect native stopping. -/
def runDriver (program : Program degree) : ℕ → Memory → Driver
  | 0, _ => idle
  | count + 1, state =>
      (routeDriver degree (fun index => Word.driver (program.table index)) state).concat
        (runDriver program count (program.advance state))















end Monodromy.CoupledContinuation.Program

/-!
## Reversible conditional control

A finite permutation of control cells is compiled into signed words of the
existing conditional loop. Its inverse is selected from the returned roots.
-/

namespace Monodromy.ReversibleControl

open CoupledContinuation

/-- None is unconditional; the Boolean requests a zero or nonzero test of one memory. -/
abbrev Guard := Option (Fin 2 × Bool)

/-- A proof interpretation of the guard; the word compiler never receives these labels. -/
def enabled (guard : Guard) (left right : ℤ) : Bool :=
  match guard with
  | none => true
  | some (register, testZero) =>
      if testZero then decide (![left, right] register = 0)
      else decide (![left, right] register ≠ 0)

def zeroGate (register : Fin 2) : Gate := if register = 0 then .zeroLeft else .zeroRight

/-- Signed repetitions of one of the two existing conditional loops. -/
def zeroWord (register : Fin 2) : ℤ → Word
  | .ofNat count => List.replicate count (zeroGate register, false)
  | .negSucc count => List.replicate (count + 1) (zeroGate register, true)

 theorem execute_zeroGate (register : Fin 2) (left right control : ℤ) :
    execute (zeroGate register).driver (prepare left right control) =
      prepare left right (control + if ![left, right] register = 0 then 1 else 0) := by
  refine Fin.cases ?_ (fun tail => ?_) register
  · exact execute_B_left left right control
  · have only : tail = 0 := Fin.eq_zero tail
    subst tail
    exact execute_B_right left right control

 theorem execute_zeroGate_reverse (register : Fin 2) (left right control : ℤ) :
    execute (zeroGate register).driver.reverse (prepare left right control) =
      prepare left right (control - if ![left, right] register = 0 then 1 else 0) := by
  have inverse := execute_driver_reverse (zeroGate register).driver
    (prepare left right (control - if ![left, right] register = 0 then 1 else 0))
  rw [execute_zeroGate] at inverse
  simpa only [sub_add_cancel] using inverse

 theorem repeat_forward (register : Fin 2) (count : ℕ) (left right control : ℤ) :
    execute (Word.driver (List.replicate count (zeroGate register, false))) (prepare left right control) =
      prepare left right (control + if ![left, right] register = 0 then (count : ℤ) else 0) := by
  induction count generalizing control with
  | zero => simp only [List.replicate_zero, execute_word_nil, Nat.cast_zero, ite_self, add_zero]
  | succ count induction_hypothesis =>
      rw [List.replicate_succ, execute_word_cons]
      change execute (Word.driver (List.replicate count (zeroGate register, false)))
        (execute (zeroGate register).driver (prepare left right control)) = _
      rw [execute_zeroGate, induction_hypothesis]
      congr 1
      split_ifs <;> push_cast <;> omega

 theorem repeat_backward (register : Fin 2) (count : ℕ) (left right control : ℤ) :
    execute (Word.driver (List.replicate count (zeroGate register, true))) (prepare left right control) =
      prepare left right (control - if ![left, right] register = 0 then (count : ℤ) else 0) := by
  induction count generalizing control with
  | zero => simp only [List.replicate_zero, execute_word_nil, Nat.cast_zero, ite_self, sub_zero]
  | succ count induction_hypothesis =>
      rw [List.replicate_succ, execute_word_cons]
      change execute (Word.driver (List.replicate count (zeroGate register, true)))
        (execute (zeroGate register).driver.reverse (prepare left right control)) = _
      rw [execute_zeroGate_reverse, induction_hypothesis]
      congr 1
      split_ifs <;> push_cast <;> omega

theorem execute_zeroWord (register : Fin 2) (amount left right control : ℤ) :
    execute (Word.driver (zeroWord register amount)) (prepare left right control) =
      prepare left right (control + if ![left, right] register = 0 then amount else 0) := by
  cases amount with
  | ofNat count => exact repeat_forward register count left right control
  | negSucc count =>
      rw [zeroWord, repeat_backward]
      congr 1
      split_ifs <;> omega

/-- All checks are actual B lifts: a nonzero guard cancels an unconditional shift only at zero. -/
def guardWord (guard : Guard) (amount : ℤ) : Word :=
  match guard with
  | none => Word.control amount
  | some (register, true) => zeroWord register amount
  | some (register, false) => Word.control amount ++ zeroWord register (-amount)

theorem execute_guardWord (guard : Guard) (amount left right control : ℤ) :
    execute (Word.driver (guardWord guard amount)) (prepare left right control) =
      prepare left right (control + if enabled guard left right then amount else 0) := by
  cases guard with
  | none => simpa [guardWord, enabled] using execute_control_word amount left right control
  | some pair =>
      rcases pair with ⟨register, testZero⟩
      cases testZero with
      | false =>
          rw [guardWord, execute_word_append, execute_control_word, execute_zeroWord]
          by_cases zero : ![left, right] register = 0 <;> simp [enabled, zero]
      | true => simpa [guardWord, enabled] using execute_zeroWord register amount left right control





variable {degree : ℕ} [NeZero degree]

def table (guard : Guard) (permutation : Equiv.Perm (Fin degree)) (index : Fin degree) : Word :=
  guardWord guard ((permutation index).val - (index.val : ℤ))

/-- The Guard is only compiler data; the native Program still has exactly table and stop. -/
def program (guard : Guard) (permutation : Equiv.Perm (Fin degree)) : Program degree :=
  ⟨table guard permutation, fun _ => false⟩



/-- The whole control quotient is retained, whichever actual memory condition enables the permutation. -/
theorem advance_prepare (guard : Guard) (permutation : Equiv.Perm (Fin degree))
    (left right quotient : ℤ) (index : Fin degree) :
    (program guard permutation).advance (prepare left right ((degree : ℤ) * quotient + index.val)) =
      if enabled guard left right then
        prepare left right ((degree : ℤ) * quotient + (permutation index).val)
      else prepare left right ((degree : ℤ) * quotient + index.val) := by
  rw [Program.advance_prepare]
  change execute (Word.driver (guardWord guard ((permutation index).val - (index.val : ℤ))))
    (prepare left right ((degree : ℤ) * quotient + index.val)) = _
  rw [execute_guardWord]
  by_cases active : enabled guard left right = true
  · rw [ite_eq_left active, ite_eq_left active]
    congr 1
    omega
  · simp only [ite_eq_right active, add_zero]

theorem inverse_prepare (guard : Guard) (permutation : Equiv.Perm (Fin degree))
    (left right quotient : ℤ) (index : Fin degree) :
    (program guard permutation.symm).advance
      ((program guard permutation).advance (prepare left right ((degree : ℤ) * quotient + index.val))) =
        prepare left right ((degree : ℤ) * quotient + index.val) := by
  rw [advance_prepare]
  by_cases active : enabled guard left right = true
  · rw [ite_eq_left active, advance_prepare, ite_eq_left active, permutation.symm_apply_apply]
  · rw [ite_eq_right active, advance_prepare, ite_eq_right active]

 theorem prepared_residue_induction {property : Memory → Prop}
    (holds : ∀ left right quotient (index : Fin degree),
      property (prepare left right ((degree : ℤ) * quotient + index.val))) (state : Memory) :
    property state := by
  obtain ⟨⟨⟨left, right⟩, control⟩, rfl⟩ := prepare_surjective state
  let index : Fin degree := ⟨(control % (degree : ℤ)).toNat, by
    apply (Int.toNat_lt_of_ne_zero (NeZero.ne degree)).mpr
    exact Int.emod_lt_of_pos _ (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne degree))⟩
  have remainder : (index.val : ℤ) = control % (degree : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast NeZero.ne degree))
  have decomposition : (degree : ℤ) * (control / (degree : ℤ)) + index.val = control := by
    rw [remainder]
    exact Int.mul_ediv_add_emod _ _
  have result := holds left right (control / (degree : ℤ)) index
  rwa [decomposition] at result

/-- The returned roots alone select a finite inverse table for the same guard. -/
theorem inverse (guard : Guard) (permutation : Equiv.Perm (Fin degree)) (state : Memory) :
    (program guard permutation.symm).advance ((program guard permutation).advance state) = state :=
  prepared_residue_induction (degree := degree)
    (property := fun point =>
      (program guard permutation.symm).advance ((program guard permutation).advance point) = point)
    (inverse_prepare guard permutation) state







def executionEquiv (guard : Guard) (permutation : Equiv.Perm (Fin degree)) : Memory ≃ Memory where
  toFun := (program guard permutation).advance
  invFun := (program guard permutation.symm).advance
  left_inv := inverse guard permutation
  right_inv := by
    intro state
    simpa only [Equiv.symm_symm] using inverse guard permutation.symm state

/-- Compatibility wrapper for the original left-zero two-PC exchange. -/
def swap : Program 2 := program (some (0, true)) (Equiv.swap (0 : Fin 2) 1)



end Monodromy.ReversibleControl

/-! Finite root-controlled memory translations use the same signed native A paths. -/

namespace Monodromy.ReversibleMemory

open CoupledContinuation

def memoryGate (register : Fin 2) : Gate := if register = 0 then .left else .right

def shiftWord (register : Fin 2) : ℤ → Word
  | .ofNat count => List.replicate count (memoryGate register, false)
  | .negSucc count => List.replicate (count + 1) (memoryGate register, true)

 theorem execute_memoryGate (register : Fin 2) (left right control : ℤ) :
    execute (memoryGate register).driver (prepare left right control) =
      prepare (left + if register = 0 then 1 else 0)
        (right + if register = 1 then 1 else 0) control := by
  refine Fin.cases ?_ (fun tail => ?_) register
  · change execute A_left _ = prepare (left + 1) (right + 0) control
    rw [add_zero]
    exact execute_A_left left right control
  · have only : tail = 0 := Fin.eq_zero tail
    subst tail
    change execute A_right _ = prepare (left + 0) (right + 1) control
    rw [add_zero]
    exact execute_A_right left right control

 theorem execute_memoryGate_reverse (register : Fin 2) (left right control : ℤ) :
    execute (memoryGate register).driver.reverse (prepare left right control) =
      prepare (left - if register = 0 then 1 else 0)
        (right - if register = 1 then 1 else 0) control := by
  refine Fin.cases ?_ (fun tail => ?_) register
  · change execute A_left.reverse _ = prepare (left - 1) (right - 0) control
    rw [sub_zero]
    exact execute_A_left_reverse left right control
  · have only : tail = 0 := Fin.eq_zero tail
    subst tail
    change execute A_right.reverse _ = prepare (left - 0) (right - 1) control
    rw [sub_zero]
    exact execute_A_right_reverse left right control

 theorem repeat_forward (register : Fin 2) (count : ℕ) (left right control : ℤ) :
    execute (Word.driver (List.replicate count (memoryGate register, false))) (prepare left right control) =
      prepare (left + if register = 0 then (count : ℤ) else 0)
        (right + if register = 1 then (count : ℤ) else 0) control := by
  induction count generalizing left right with
  | zero => simp only [List.replicate_zero, execute_word_nil, Nat.cast_zero, ite_self, add_zero]
  | succ count induction_hypothesis =>
      rw [List.replicate_succ, execute_word_cons]
      change execute (Word.driver (List.replicate count (memoryGate register, false)))
        (execute (memoryGate register).driver (prepare left right control)) = _
      rw [execute_memoryGate, induction_hypothesis]
      congr 1 <;> split_ifs <;> push_cast <;> omega

 theorem repeat_backward (register : Fin 2) (count : ℕ) (left right control : ℤ) :
    execute (Word.driver (List.replicate count (memoryGate register, true))) (prepare left right control) =
      prepare (left - if register = 0 then (count : ℤ) else 0)
        (right - if register = 1 then (count : ℤ) else 0) control := by
  induction count generalizing left right with
  | zero => simp only [List.replicate_zero, execute_word_nil, Nat.cast_zero, ite_self, sub_zero]
  | succ count induction_hypothesis =>
      rw [List.replicate_succ, execute_word_cons]
      change execute (Word.driver (List.replicate count (memoryGate register, true)))
        (execute (memoryGate register).driver.reverse (prepare left right control)) = _
      rw [execute_memoryGate_reverse, induction_hypothesis]
      congr 1 <;> split_ifs <;> push_cast <;> omega

theorem execute_shiftWord (register : Fin 2) (amount left right control : ℤ) :
    execute (Word.driver (shiftWord register amount)) (prepare left right control) =
      prepare (left + if register = 0 then amount else 0)
        (right + if register = 1 then amount else 0) control := by
  cases amount with
  | ofNat count => exact repeat_forward register count left right control
  | negSucc count =>
      rw [shiftWord, repeat_backward]
      congr 1 <;> split_ifs <;> omega

/-- A static displacement is two finite signed words in the original memory loops. -/
def memoryWord (move : ℤ × ℤ) : Word := shiftWord 0 move.1 ++ shiftWord 1 move.2

theorem execute_memoryWord (move : ℤ × ℤ) (left right control : ℤ) :
    execute (Word.driver (memoryWord move)) (prepare left right control) =
      prepare (left + move.1) (right + move.2) control := by
  simp [memoryWord, execute_word_append, execute_shiftWord]





/-- Actual lower translations leave every upper finite-root observation unchanged. -/
theorem controlRoot_memoryWord (degree : ℕ) [NeZero degree] (move : ℤ × ℤ) (state : Memory) :
    controlRoot degree (execute (Word.driver (memoryWord move)) state) = controlRoot degree state := by
  obtain ⟨⟨⟨left, right⟩, control⟩, rfl⟩ := prepare_surjective state
  rw [execute_memoryWord, controlRoot_prepare, controlRoot_prepare]

 theorem memoryWord_inverse (move : ℤ × ℤ) (state : Memory) :
    execute (Word.driver (memoryWord (-move.1, -move.2)))
      (execute (Word.driver (memoryWord move)) state) = state := by
  obtain ⟨⟨⟨left, right⟩, control⟩, rfl⟩ := prepare_surjective state
  rw [execute_memoryWord, execute_memoryWord]
  simp

variable {degree : ℕ} [NeZero degree]

def negate (moves : Fin degree → ℤ × ℤ) : Fin degree → ℤ × ℤ :=
  fun index => (-(moves index).1, -(moves index).2)

/-- The table contains only static finite words; it never receives a memory state. -/
def program (moves : Fin degree → ℤ × ℤ) : Program degree :=
  ⟨fun index => memoryWord (moves index), fun _ => false⟩





 theorem advance_of_root (moves : Fin degree → ℤ × ℤ) (state : Memory) (index : Fin degree)
    (observed : controlRoot degree state = (Radix.omega degree index : ℂ)) :
    (program moves).advance state = execute (Word.driver (memoryWord (moves index))) state :=
  executeRouted_eq degree (fun index => Word.driver (memoryWord (moves index))) state index observed

/-- The unchanged returned control root selects the negated update, with no retained history. -/
theorem inverse (moves : Fin degree → ℤ × ℤ) (state : Memory) :
    (program (negate moves)).advance ((program moves).advance state) = state := by
  obtain ⟨index, observed⟩ := controlRoot_is_root degree state
  have moved : controlRoot degree (execute (Word.driver (memoryWord (moves index))) state) =
      (Radix.omega degree index : ℂ) :=
    (controlRoot_memoryWord degree (moves index) state).trans observed
  rw [advance_of_root moves state index observed, advance_of_root (negate moves) _ index moved]
  exact memoryWord_inverse (moves index) state

omit [NeZero degree] in
@[simp] theorem negate_negate (moves : Fin degree → ℤ × ℤ) : negate (negate moves) = moves := by
  funext index
  simp [negate]

def executionEquiv (moves : Fin degree → ℤ × ℤ) : Memory ≃ Memory where
  toFun := (program moves).advance
  invFun := (program (negate moves)).advance
  left_inv := inverse moves
  right_inv := by
    intro state
    simpa only [negate_negate] using inverse (negate moves) state

end Monodromy.ReversibleMemory


/-!
## Integer coordinates of actual returned roots

These coordinates state and prove the action of the existing geometric execution.
They do not participate in path generation or add an execution rule.
-/

namespace Monodromy.CoupledContinuation

/-- Integer labels are a proof interpretation, never an input to native path generation. -/
abbrev Labels := (ℤ × ℤ) × ℤ

def Labels.prepare (labels : Labels) : Memory := Monodromy.CoupledContinuation.prepare labels.1.1 labels.1.2 labels.2

/-- Proof-side arithmetic of one of the actual five loops or its reverse. -/
def Gate.evalInt (gate : Gate) (backward : Bool) (labels : Labels) : Labels :=
  let displacement : ℤ := if backward then -1 else 1
  match gate with
  | .left => ((labels.1.1 + displacement, labels.1.2), labels.2)
  | .right => ((labels.1.1, labels.1.2 + displacement), labels.2)
  | .zeroLeft => (labels.1, labels.2 + if labels.1.1 = 0 then displacement else 0)
  | .zeroRight => (labels.1, labels.2 + if labels.1.2 = 0 then displacement else 0)
  | .control => (labels.1, labels.2 + displacement)

def Word.evalInt : Word → Labels → Labels
  | [], labels => labels
  | (gate, backward) :: rest, labels => Word.evalInt rest (Gate.evalInt gate backward labels)

/-- All arithmetic cases are derived from native transport, including reverse conditional gates. -/
theorem Gate.execute_evalInt (gate : Gate) (backward : Bool) (labels : Labels) :
    execute (if backward then gate.driver.reverse else gate.driver) (Labels.prepare labels) =
      Labels.prepare (Gate.evalInt gate backward labels) := by
  rcases labels with ⟨⟨left, right⟩, control⟩
  cases gate with
  | left =>
      cases backward with
      | false => simpa [Gate.driver, Gate.evalInt, Labels.prepare] using execute_A_left left right control
      | true => simpa [Gate.driver, Gate.evalInt, Labels.prepare, sub_eq_add_neg] using execute_A_left_reverse left right control
  | right =>
      cases backward with
      | false => simpa [Gate.driver, Gate.evalInt, Labels.prepare] using execute_A_right left right control
      | true => simpa [Gate.driver, Gate.evalInt, Labels.prepare, sub_eq_add_neg] using execute_A_right_reverse left right control
  | zeroLeft =>
      cases backward with
      | false => simpa [Gate.driver, Gate.evalInt, Labels.prepare] using execute_B_left left right control
      | true =>
          have inverse := execute_driver_reverse B_left
            (prepare left right (control - if left = 0 then 1 else 0))
          rw [execute_B_left] at inverse
          simp only [sub_add_cancel] at inverse
          by_cases zero : left = 0 <;>
            simpa [Gate.driver, Gate.evalInt, Labels.prepare, zero, sub_eq_add_neg] using inverse
  | zeroRight =>
      cases backward with
      | false => simpa [Gate.driver, Gate.evalInt, Labels.prepare] using execute_B_right left right control
      | true =>
          have inverse := execute_driver_reverse B_right
            (prepare left right (control - if right = 0 then 1 else 0))
          rw [execute_B_right] at inverse
          simp only [sub_add_cancel] at inverse
          by_cases zero : right = 0 <;>
            simpa [Gate.driver, Gate.evalInt, Labels.prepare, zero, sub_eq_add_neg] using inverse
  | control =>
      cases backward with
      | false => simpa [Gate.driver, Gate.evalInt, Labels.prepare] using execute_control_prepare left right control
      | true => simpa [Gate.driver, Gate.evalInt, Labels.prepare, sub_eq_add_neg] using execute_control_reverse left right control

theorem Word.execute_evalInt (word : Word) (labels : Labels) :
    execute (Word.driver word) (Labels.prepare labels) = Labels.prepare (Word.evalInt word labels) := by
  induction word generalizing labels with
  | nil => exact execute_word_nil (Labels.prepare labels)
  | cons atom rest recursive =>
      rcases atom with ⟨gate, backward⟩
      rw [execute_word_cons, Gate.execute_evalInt, recursive]
      rfl

namespace Program

variable {degree : ℕ} [NeZero degree]

/-- Euclidean residues describe, but do not implement, finite-root routing. -/
def indexInt (degree : ℕ) [NeZero degree] (labels : Labels) : Fin degree :=
  ⟨(labels.2 % (degree : ℤ)).toNat, by
    apply (Int.toNat_lt_of_ne_zero (NeZero.ne degree)).mpr
    exact Int.emod_lt_of_pos _ (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne degree))⟩

def nextInt (program : Program degree) (labels : Labels) : Labels :=
  Word.evalInt (program.table (indexInt degree labels)) labels

def haltInt (program : Program degree) (labels : Labels) : Bool :=
  program.stop (indexInt degree labels)

def stepInt (program : Program degree) (labels : Labels) : Option Labels :=
  if program.haltInt labels then none else some (program.nextInt labels)

def evalInt (program : Program degree) : Labels → Part Labels :=
  StateTransition.eval program.stepInt

theorem indexInt_cast (labels : Labels) :
    ((indexInt degree labels).val : ℤ) = labels.2 % (degree : ℤ) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast NeZero.ne degree))

theorem control_decomposition (labels : Labels) :
    (degree : ℤ) * (labels.2 / (degree : ℤ)) + (indexInt degree labels).val = labels.2 := by
  rw [indexInt_cast]
  exact Int.mul_ediv_add_emod _ _

theorem advance_prepareInt (program : Program degree) (labels : Labels) :
    program.advance (Labels.prepare labels) = Labels.prepare (program.nextInt labels) := by
  have actual := program.advance_prepare labels.1.1 labels.1.2
    (labels.2 / (degree : ℤ)) (indexInt degree labels)
  rw [control_decomposition] at actual
  exact actual.trans (Word.execute_evalInt _ labels)









end Program

end Monodromy.CoupledContinuation


/-!
## Finite cyclic staging in the existing upper branch

The compiler emits only the existing signed geometric words. A finite stage is
packed into the upper branch, and every generated word is executed by the
unchanged native lifting kernel.
-/

namespace Monodromy.StagedProgram

open CoupledContinuation
open Fin.NatCast

/-- Scaling changes only the upper branch displacement, never the two memory coordinates. -/
def pack (factor : ℕ) (phase : ℤ) (labels : Labels) : Labels :=
  (labels.1, (factor : ℤ) * labels.2 + phase)

def scaleAtom (factor : ℕ) (atom : Gate × Bool) : Word :=
  match atom.1 with
  | .left | .right => [atom]
  | _ => List.replicate factor atom

def scaleWord (factor : ℕ) : Word → Word
  | [] => []
  | atom :: rest => scaleAtom factor atom ++ scaleWord factor rest

 theorem eval_append (first second : Word) (labels : Labels) :
    Word.evalInt (first ++ second) labels =
      Word.evalInt second (Word.evalInt first labels) := by
  induction first generalizing labels with
  | nil => rfl
  | cons atom rest recursive => simpa only [List.cons_append, Word.evalInt] using recursive _

 theorem repeat_shear (atom : Gate × Bool) (memory : ℤ × ℤ) (amount : ℤ)
    (action : ∀ control, Gate.evalInt atom.1 atom.2 (memory, control) = (memory, control + amount))
    (count : ℕ) (control : ℤ) :
    Word.evalInt (List.replicate count atom) (memory, control) =
      (memory, control + (count : ℤ) * amount) := by
  induction count generalizing control with
  | zero => simp [Word.evalInt]
  | succ count recursive =>
      rw [List.replicate_succ, Word.evalInt, action, recursive]
      congr 1
      push_cast
      ring

theorem scaleAtom_eval (factor : ℕ) (phase : ℤ) (atom : Gate × Bool) (labels : Labels) :
    Word.evalInt (scaleAtom factor atom) (pack factor phase labels) =
      pack factor phase (Gate.evalInt atom.1 atom.2 labels) := by
  rcases atom with ⟨gate, backward⟩
  rcases labels with ⟨⟨left, right⟩, control⟩
  cases gate with
  | left => simp [scaleAtom, Word.evalInt, Gate.evalInt, pack]
  | right => simp [scaleAtom, Word.evalInt, Gate.evalInt, pack]
  | zeroLeft =>
      have repeated := repeat_shear (.zeroLeft, backward) (left, right)
        (if left = 0 then (if backward then -1 else 1) else 0) (fun _ => rfl)
        factor ((factor : ℤ) * control + phase)
      change Word.evalInt (List.replicate factor (.zeroLeft, backward)) _ = _
      dsimp only [pack]
      rw [repeated]
      simp only [Gate.evalInt]
      congr 1
      ring
  | zeroRight =>
      have repeated := repeat_shear (.zeroRight, backward) (left, right)
        (if right = 0 then (if backward then -1 else 1) else 0) (fun _ => rfl)
        factor ((factor : ℤ) * control + phase)
      change Word.evalInt (List.replicate factor (.zeroRight, backward)) _ = _
      dsimp only [pack]
      rw [repeated]
      simp only [Gate.evalInt]
      congr 1
      ring
  | control =>
      have repeated := repeat_shear (.control, backward) (left, right)
        (if backward then -1 else 1) (fun _ => rfl)
        factor ((factor : ℤ) * control + phase)
      change Word.evalInt (List.replicate factor (.control, backward)) _ = _
      dsimp only [pack]
      rw [repeated]
      simp only [Gate.evalInt]
      congr 1
      ring

theorem scaleWord_eval (factor : ℕ) (phase : ℤ) (word : Word) (labels : Labels) :
    Word.evalInt (scaleWord factor word) (pack factor phase labels) =
      pack factor phase (Word.evalInt word labels) := by
  induction word generalizing labels with
  | nil => rfl
  | cons atom rest recursive =>
      rw [scaleWord, eval_append, scaleAtom_eval, recursive]
      rfl

theorem execute_scaleWord (factor : ℕ) (phase : ℤ) (word : Word) (labels : Labels) :
    execute (Word.driver (scaleWord factor word)) (Labels.prepare (pack factor phase labels)) =
      Labels.prepare (pack factor phase (Word.evalInt word labels)) := by
  rw [Word.execute_evalInt, scaleWord_eval]

def labelsEquiv : Labels ≃ Memory :=
  Equiv.ofBijective Labels.prepare ⟨prepare_injective, prepare_surjective⟩

variable (count degree : ℕ) [NeZero count] [NeZero degree]

/-- The finite stage is packed in the same upper integer branch. -/
def packing : Labels × Fin count ≃ Labels :=
  Equiv.ofBijective (fun pair => pack count pair.2.val pair.1) (by
    constructor
    · rintro ⟨first, phase⟩ ⟨second, other⟩ same
      have memories := congrArg (fun labels : Labels => labels.1) same
      change first.1 = second.1 at memories
      have controls : (count : ℤ) * first.2 + phase.val =
          (count : ℤ) * second.2 + other.val := congrArg (fun labels : Labels => labels.2) same
      have phase_mod (stage : Fin count) (control : ℤ) :
          ((count : ℤ) * control + stage.val) % (count : ℤ) = stage.val := by
        rw [add_comm, Int.add_mul_emod_self_left,
          Int.emod_eq_of_lt (by omega) (by exact_mod_cast stage.isLt)]
      have phases := congrArg (fun value : ℤ => value % (count : ℤ)) controls
      rw [phase_mod, phase_mod] at phases
      have phase_eq : phase = other := Fin.ext (by exact_mod_cast phases)
      subst other
      have counters : first.2 = second.2 := by
        apply (mul_right_injective₀ (by exact_mod_cast NeZero.ne count : (count : ℤ) ≠ 0))
        exact (add_right_cancel controls)
      exact Prod.ext (Prod.ext memories counters) rfl
    · intro labels
      refine ⟨((labels.1, labels.2 / (count : ℤ)), Program.indexInt count labels), ?_⟩
      exact Prod.ext rfl (Program.control_decomposition labels))

def packedEquiv : Memory × Fin count ≃ Memory :=
  (Equiv.prodCongr labelsEquiv.symm (Equiv.refl _)).trans
    ((packing count).trans labelsEquiv)

def embed (phase : Fin count) (state : Memory) : Memory := packedEquiv count (state, phase)

@[simp] theorem embed_prepare (phase : Fin count) (labels : Labels) :
    embed count phase (Labels.prepare labels) = Labels.prepare (pack count phase.val labels) := by
  change labelsEquiv (pack count phase.val (labelsEquiv.symm (labelsEquiv labels))) = _
  rw [labelsEquiv.symm_apply_apply]
  rfl

def address : Fin degree × Fin count ≃ Fin (count * degree) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm degree count))

omit [NeZero count] [NeZero degree] in
theorem address_val (index : Fin degree) (phase : Fin count) :
    ((address count degree (index, phase)).val : ℤ) =
      (count : ℤ) * index.val + phase.val := by
  simp [address, finProdFinEquiv]
  ring

def clock (phase : Fin count) : ℤ :=
  ((finRotate count phase).val : ℤ) - phase.val

/-- The table consists solely of the existing words followed by a finite clock word. -/
def compile (stages : Fin count → Program degree) : Program (count * degree) where
  table index :=
    let pair := (address count degree).symm index
    scaleWord count ((stages pair.2).table pair.1) ++ Word.control (clock count pair.2)
  stop _ := false

omit [NeZero count] [NeZero degree] in
theorem compile_table (stages : Fin count → Program degree)
    (index : Fin degree) (phase : Fin count) :
    (compile count degree stages).table (address count degree (index, phase)) =
      scaleWord count ((stages phase).table index) ++ Word.control (clock count phase) := by
  simp [compile]

omit [NeZero count] in
theorem execute_stageWord (phase : Fin count) (word : Word) (labels : Labels) :
    execute (Word.driver (scaleWord count word ++ Word.control (clock count phase)))
      (Labels.prepare (pack count phase.val labels)) =
      Labels.prepare (pack count (finRotate count phase).val (Word.evalInt word labels)) := by
  rw [execute_word_append, execute_scaleWord]
  change execute (Word.driver (Word.control (clock count phase)))
    (prepare _ _ _) = prepare _ _ _
  rw [execute_control_word]
  congr 1
  simp [pack, clock]

theorem advance_prepare (stages : Fin count → Program degree)
    (left right quotient : ℤ) (index : Fin degree) (phase : Fin count) :
    (compile count degree stages).advance
      (prepare left right ((count : ℤ) * ((degree : ℤ) * quotient + index.val) + phase.val)) =
      Labels.prepare (pack count (finRotate count phase).val
        (Word.evalInt ((stages phase).table index)
          ((left, right), (degree : ℤ) * quotient + index.val))) := by
  have actual := (compile count degree stages).advance_prepare left right quotient
    (address count degree (index, phase))
  rw [compile_table] at actual
  have control :
      ((count * degree : ℕ) : ℤ) * quotient + (address count degree (index, phase)).val =
        (count : ℤ) * ((degree : ℤ) * quotient + index.val) + phase.val := by
    rw [address_val]
    push_cast
    ring
  rw [control] at actual
  apply actual.trans
  exact execute_stageWord count phase ((stages phase).table index)
    ((left, right), (degree : ℤ) * quotient + index.val)

theorem advance_embed (stages : Fin count → Program degree)
    (phase : Fin count) (state : Memory) :
    (compile count degree stages).advance (embed count phase state) =
      embed count (finRotate count phase) ((stages phase).advance state) := by
  obtain ⟨labels, rfl⟩ := labelsEquiv.surjective state
  change (compile count degree stages).advance (embed count phase (Labels.prepare labels)) =
    embed count (finRotate count phase) ((stages phase).advance (Labels.prepare labels))
  rw [embed_prepare, (stages phase).advance_prepareInt, embed_prepare]
  have actual := advance_prepare count degree stages labels.1.1 labels.1.2
    (labels.2 / (degree : ℤ)) (Program.indexInt degree labels) phase
  rw [Program.control_decomposition] at actual
  exact actual














/-- The backward clock changes stage while retaining the unpacked upper control. -/
def backClock (phase : Fin count) : ℤ :=
  (((finRotate count).symm phase).val : ℤ) - phase.val

/-- The inverse is another table of the same native words, selected from the returned roots. -/
def compileReverse (backward : Fin count → Program degree) : Program (count * degree) where
  table index :=
    let pair := (address count degree).symm index
    Word.control (backClock count pair.2) ++
      scaleWord count ((backward ((finRotate count).symm pair.2)).table pair.1)
  stop _ := false

omit [NeZero count] [NeZero degree] in
theorem compileReverse_table (backward : Fin count → Program degree)
    (index : Fin degree) (phase : Fin count) :
    (compileReverse count degree backward).table (address count degree (index, phase)) =
      Word.control (backClock count phase) ++
        scaleWord count ((backward ((finRotate count).symm phase)).table index) := by
  simp [compileReverse]

omit [NeZero count] in
theorem execute_reverseWord (phase : Fin count) (word : Word) (labels : Labels) :
    execute (Word.driver (Word.control (backClock count phase) ++ scaleWord count word))
      (Labels.prepare (pack count phase.val labels)) =
      Labels.prepare (pack count ((finRotate count).symm phase).val (Word.evalInt word labels)) := by
  rw [execute_word_append]
  change execute (Word.driver (scaleWord count word))
    (execute (Word.driver (Word.control (backClock count phase))) (prepare _ _ _)) = _
  rw [execute_control_word]
  dsimp only [pack]
  have clock_value : (count : ℤ) * labels.2 + phase.val + backClock count phase =
      (count : ℤ) * labels.2 + ((finRotate count).symm phase).val := by
    simp [backClock]
  rw [clock_value]
  exact execute_scaleWord count ((finRotate count).symm phase).val word labels

theorem reverse_advance_prepare (backward : Fin count → Program degree)
    (left right quotient : ℤ) (index : Fin degree) (phase : Fin count) :
    (compileReverse count degree backward).advance
      (prepare left right ((count : ℤ) * ((degree : ℤ) * quotient + index.val) + phase.val)) =
      Labels.prepare (pack count ((finRotate count).symm phase).val
        (Word.evalInt ((backward ((finRotate count).symm phase)).table index)
          ((left, right), (degree : ℤ) * quotient + index.val))) := by
  have actual := (compileReverse count degree backward).advance_prepare left right quotient
    (address count degree (index, phase))
  rw [compileReverse_table] at actual
  have control :
      ((count * degree : ℕ) : ℤ) * quotient + (address count degree (index, phase)).val =
        (count : ℤ) * ((degree : ℤ) * quotient + index.val) + phase.val := by
    rw [address_val]
    push_cast
    ring
  rw [control] at actual
  apply actual.trans
  exact execute_reverseWord count phase
    ((backward ((finRotate count).symm phase)).table index)
    ((left, right), (degree : ℤ) * quotient + index.val)

theorem reverse_advance_embed (backward : Fin count → Program degree)
    (phase : Fin count) (state : Memory) :
    (compileReverse count degree backward).advance (embed count phase state) =
      embed count ((finRotate count).symm phase)
        ((backward ((finRotate count).symm phase)).advance state) := by
  obtain ⟨labels, rfl⟩ := labelsEquiv.surjective state
  change (compileReverse count degree backward).advance (embed count phase (Labels.prepare labels)) =
    embed count ((finRotate count).symm phase)
      ((backward ((finRotate count).symm phase)).advance (Labels.prepare labels))
  rw [embed_prepare, (backward ((finRotate count).symm phase)).advance_prepareInt, embed_prepare]
  have actual := reverse_advance_prepare count degree backward labels.1.1 labels.1.2
    (labels.2 / (degree : ℤ)) (Program.indexInt degree labels) phase
  rw [Program.control_decomposition] at actual
  exact actual

theorem left_inverse (forward backward : Fin count → Program degree)
    (inverse : ∀ phase, Function.LeftInverse (backward phase).advance (forward phase).advance) :
    Function.LeftInverse (compileReverse count degree backward).advance
      (compile count degree forward).advance := by
  intro state
  obtain ⟨⟨point, phase⟩, rfl⟩ := (packedEquiv count).surjective state
  change (compileReverse count degree backward).advance
    ((compile count degree forward).advance (embed count phase point)) = embed count phase point
  rw [advance_embed, reverse_advance_embed, Equiv.symm_apply_apply, inverse]

theorem right_inverse (forward backward : Fin count → Program degree)
    (inverse : ∀ phase, Function.RightInverse (backward phase).advance (forward phase).advance) :
    Function.RightInverse (compileReverse count degree backward).advance
      (compile count degree forward).advance := by
  intro state
  obtain ⟨⟨point, phase⟩, rfl⟩ := (packedEquiv count).surjective state
  change (compile count degree forward).advance
    ((compileReverse count degree backward).advance (embed count phase point)) = embed count phase point
  rw [reverse_advance_embed, advance_embed, Equiv.apply_symm_apply, inverse]

def executionEquiv (forward backward : Fin count → Program degree)
    (left : ∀ phase, Function.LeftInverse (backward phase).advance (forward phase).advance)
    (right : ∀ phase, Function.RightInverse (backward phase).advance (forward phase).advance) :
    Memory ≃ Memory where
  toFun := (compile count degree forward).advance
  invFun := (compileReverse count degree backward).advance
  left_inv := left_inverse count degree forward backward left
  right_inv := right_inverse count degree forward backward right


end Monodromy.StagedProgram

/-! Static phase-zero stopping for the existing finite-stage compiler. -/

namespace Monodromy.StagedProgram

open CoupledContinuation
open Fin.NatCast

variable (count degree : ℕ) [NeZero count] [NeZero degree]

/-- The same finite words, stopped only at selected packed phase-zero addresses. -/
def markedCompile (stages : Fin count → Program degree) (mark : Fin degree → Bool) :
    Program (count * degree) where
  table := (compile count degree stages).table
  stop index :=
    let pair := (address count degree).symm index
    if pair.2 = 0 then mark pair.1 else false















/-- A phase-zero boundary is an actual power-cover root, not a stored clock register. -/
def PhaseBoundary (state : Memory) : Prop := controlRoot count state = 1













end Monodromy.StagedProgram

/-! First-return predecessor uniqueness for reversible advances. -/

namespace Monodromy.ReversibleReturn

variable {State Source : Type*}

/-- A positive return with no earlier positive visit to the same boundary. -/
def FirstReturn (advance : State → State) (boundary : State → Prop) (first last : State) : Prop :=
  ∃ count : ℕ, 0 < count ∧ advance^[count] first = last ∧ boundary first ∧ boundary last ∧
    ∀ middle : ℕ, 0 < middle → middle < count → ¬ boundary (advance^[middle] first)







end Monodromy.ReversibleReturn


/-! Marked inverse execution and first-return transport. -/

namespace Monodromy.CoupledContinuation.Program

noncomputable section

variable {degree : ℕ} [NeZero degree]

/-- Run the inverse word table, stopping at the same finite root marks. -/
def boundaryInverse (backward boundary : Program degree) : Program degree :=
  { backward with stop := boundary.stop }

/-- Leave the current mark once, then use the inverse words until the next mark. -/
def reverseReturn (backward boundary : Program degree) (state : Memory) : Part Memory :=
  (boundaryInverse backward boundary).eval (backward.advance state)



end

end Monodromy.CoupledContinuation.Program

namespace Monodromy.ReversibleReturn

variable {State : Type*}





end Monodromy.ReversibleReturn


